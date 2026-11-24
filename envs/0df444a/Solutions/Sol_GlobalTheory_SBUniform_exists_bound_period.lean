-- Prove2me | solution 1 for GlobalTheory.SBUniform.exists_bound_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:06.350075+00:00
-- url     : https://prove2.me/submissions/8883c13a-6dc2-491b-9af3-d656f9a7e72f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Theorems.Thm_GlobalTheory_SBUniform_isOpen_deep
import Theorems.Thm_GlobalTheory_SBUniform_exists_deep_subset
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open Filter Topology
namespace GlobalTheory.SBUniform
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem deep_neg {a : ℤ} {x : k} (h : Deep a x) : Deep a (-x) := by
  unfold Deep at h ⊢
  rwa [Valuation.map_neg]
private theorem deep_add {a : ℤ} {x y : k} (hx : Deep a x) (hy : Deep a y) : Deep a (x + y) := by
  unfold Deep at hx hy ⊢
  exact ((valuation k).map_add x y).trans (max_le hx hy)
private theorem deep_zero' (a : ℤ) : Deep a (0 : k) := by
  unfold Deep
  simp
private theorem deep_of_le' {a b : ℤ} (hab : a ≤ b) {x : k} (h : Deep b x) : Deep a x := by
  unfold Deep at h ⊢
  exact h.trans (zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab)
private theorem exists_deep_neg_natCast (x : k) : ∃ N : ℕ, Deep (-(N : ℤ)) x := by
  unfold Deep
  by_cases hx : valuation k x = 0
  · exact ⟨0, by simp [hx]⟩

  obtain ⟨N, hN⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) (Units.mk0 _ (inv_ne_zero hx))
  refine ⟨N, ?_⟩
  rw [Units.val_mk0] at hN
  have hpos : (0 : ValueGroupWithZero k) < uniformizer k ^ N := pow_pos uniformizer_pos N
  have hx0 : (0 : ValueGroupWithZero k) < valuation k x := zero_lt_iff.2 hx
  rw [_root_.zpow_neg, zpow_natCast]
  exact ((lt_inv_comm₀ hpos hx0).1 hN).le
private theorem isOpen_setOf_forall_deep {n : Type} [Fintype n] (a : ℤ) :
    IsOpen {y : Matrix n n k | ∀ i j, Deep a (y i j)} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_deep (k := k) a).preimage (continuous_id.matrix_elem i j)
end GlobalTheory.SBUniform
end

set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open Filter Topology
open GlobalTheory GlobalTheory.SBUniform
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SBUniform
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n], ∀ Φ ∈ SB (Matrix n n k),
    ∃ N M : ℕ, (∀ x, Φ x ≠ 0 → ∀ i j, Deep (-(N : ℤ)) (x i j)) ∧
      ∀ x y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x := by
  intro k _ _ _ _ n _ _ Φ hΦ
  have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨hlc, hcs⟩ := hΦ'
  have hC : IsCompact (tsupport Φ) := hcs
  have hzero : ∀ z, z ∉ tsupport Φ → Φ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport Φ h)

  let U : ℕ → Set (Matrix n n k) := fun N => {x | ∀ i j, Deep (-(N : ℤ)) (x i j)}
  have hUm : Monotone U := fun N N' h x hx i j =>
    deep_of_le' (neg_le_neg (by exact_mod_cast h)) (hx i j)
  have hUcov : tsupport Φ ⊆ ⋃ N, U N := by
    intro x _
    have hev : ∀ᶠ N : ℕ in atTop, ∀ i j, Deep (-(N : ℤ)) (x i j) := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      obtain ⟨N₀, hN₀⟩ := exists_deep_neg_natCast (x i j)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact deep_of_le' (neg_le_neg (by exact_mod_cast hN)) hN₀
    obtain ⟨N, hN⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨N, hN⟩
  obtain ⟨N, hN⟩ := hC.elim_directed_cover U (fun N => isOpen_setOf_forall_deep _) hUcov hUm.directed_le

  let W : ℕ → Set (Matrix n n k) :=
    fun M => {x | ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x}
  have hWm : Monotone W := fun M M' h x hx y hy =>
    hx y fun i j => deep_of_le' (by exact_mod_cast h) (hy i j)
  have hWo : ∀ M, IsOpen (W M) := by
    intro M
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hD : {y : Matrix n n k | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 (0 : Matrix n n k) :=
      (isOpen_setOf_forall_deep _).mem_nhds fun i j => deep_zero' _
    have hD' : (fun z : Matrix n n k => z - x) ⁻¹' {y | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 x := by
      apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      simpa using hD
    refine Filter.mem_of_superset hD' fun z hz y hy => ?_
    have hz' : ∀ i j, Deep (M : ℤ) ((z - x) i j) := hz
    have h1 : Φ (x + ((z - x) + y)) = Φ x :=
      hx _ fun i j => by simpa using deep_add (hz' i j) (hy i j)
    have h2 : Φ (x + (z - x)) = Φ x := hx _ hz'
    rw [add_sub_cancel] at h2
    have he : x + ((z - x) + y) = z + y := by abel
    rw [he] at h1
    rw [h1, h2]
  have hWcov : tsupport Φ ⊆ ⋃ M, W M := by
    intro x _
    have hs : {y : Matrix n n k | Φ (x + y) = Φ x} ∈ 𝓝 (0 : Matrix n n k) := by
      apply IsOpen.mem_nhds
      · exact (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
      · simp
    obtain ⟨M, hM⟩ := exists_deep_subset hs
    exact Set.mem_iUnion.2 ⟨M, fun y hy => hM y hy⟩
  obtain ⟨M, hM⟩ := hC.elim_directed_cover W hWo hWcov hWm.directed_le
  refine ⟨N, M, fun x hx i j => hN (subset_tsupport Φ hx) i j, fun x y hy => ?_⟩
  by_cases hx : x ∈ tsupport Φ
  · exact hM hx y hy
  by_cases hxy : x + y ∈ tsupport Φ
  · have h := hM hxy (-y) fun i j => by simpa using deep_neg (hy i j)
    rw [add_neg_cancel_right] at h
    exact h.symm
  · rw [hzero _ hx, hzero _ hxy]
end GlobalTheory.SBUniform
