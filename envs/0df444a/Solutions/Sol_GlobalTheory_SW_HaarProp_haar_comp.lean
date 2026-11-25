-- Prove2me | solution 1 for GlobalTheory.SW.HaarProp.haar_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:41.335195+00:00
-- url     : https://prove2.me/submissions/cd21fe23-a042-46a6-8829-3addb6ff9a64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
import Theorems.Thm_P2M_GlobalTheory_SW_HaarProp_mem_perSub__3963e3e4477d
import Theorems.Thm_GlobalTheory_SW_HaarProp_transport
import Theorems.Thm_GlobalTheory_SW_Dict_isSB_comp
import Theorems.Thm_GlobalTheory_SW_HaarLevel_finite_support
import Theorems.Thm_GlobalTheory_SW_HaarLevel_finsum_quotient_of_le
import Theorems.Thm_GlobalTheory_SW_HaarLevel_haarAt_mul
import Theorems.Thm_GlobalTheory_SW_HaarLevel_nsmul_cancel
import Theorems.Thm_GlobalTheory_SW_HaarLevel_perSub_le
import Theorems.Thm_GlobalTheory_SW_HaarLevel_periodic
import Theorems.Thm_GlobalTheory_SW_HaarLevel_relIndex_perSub
import Theorems.Thm_GlobalTheory_SW_haar_eq_haarAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarProp
open HaarLevel
variable {K K' κ ι κ' ι' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
  [Fintype κ] [Fintype ι] [Fintype κ'] [Fintype ι']
namespace GlobalTheory.SW.HaarProp
theorem _root_.solution (e : Matrix κ ι K ≃+ Matrix κ' ι' K') (D D' : ℕ) (hD : 0 < D) (hD' : 0 < D')
    (h1 : ∀ x, IntM x → IntM (D • e x)) (h2 : ∀ x, IntM x → IntM (D' • e.symm x))
    (hd : Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) =
      Module.finrank ℚ K' * (Fintype.card κ' * Fintype.card ι')) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix κ' ι' K' → ℂ, IsSB φ → haar (fun m => φ (e m)) = c * haar φ := by
  set d := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) with hdd
  let t : ℕ → AddSubgroup (Matrix κ ι K) := fun R => (perSub K' κ' ι' R).comap e.toAddMonoidHom
  have ht : ∀ R x, x ∈ t R ↔ ∃ y, IntM y ∧ R • y = e x := fun R x => mem_perSub' R (e x)
  have hle : ∀ R, perSub K κ ι (R * D) ≤ t R := by
    intro R x hx
    obtain ⟨y, hy, rfl⟩ := (mem_perSub' _ _).1 hx
    exact (ht _ _).2 ⟨_, h1 y hy, by rw [map_nsmul, mul_smul]⟩
  have hne : (perSub K κ ι D).relIndex (t 1) ≠ 0 := by
    have hle' : t (1 * (D * D')) ≤ perSub K κ ι D := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := (ht _ _).1 hx
      refine (mem_perSub' _ _).2 ⟨_, h2 y hy, ?_⟩
      rw [← mul_smul, ← map_nsmul, ← one_mul (D * D'), hxy, e.symm_apply_apply]
    have h0 : (t (1 * (D * D'))).relIndex (t 1) ≠ 0 := by
      rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective e.surjective,
        relIndex_perSub _ _ one_pos]
      positivity
    exact fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle' h)
  have hsc : ∀ R, 0 < R → (perSub K κ ι (R * D)).relIndex (t R) =
      (perSub K κ ι D).relIndex (t 1) := by
    intro R hR
    have ha : (perSub K κ ι (R * D)).comap (nsmulAddMonoidHom R) = perSub K κ ι D := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_perSub', nsmulAddMonoidHom_apply, mul_smul,
        nsmul_cancel hR]
    have hb : (t 1).map (nsmulAddMonoidHom R) = t R := by
      ext x
      simp only [AddSubgroup.mem_map, ht, nsmulAddMonoidHom_apply, one_smul]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨_, hz, by rw [map_nsmul]⟩
      · rintro ⟨y, hy, hxy⟩
        refine ⟨e.symm y, ⟨y, hy, by simp⟩, ?_⟩
        rw [← map_nsmul, hxy, e.symm_apply_apply]
    rw [← ha, AddSubgroup.relIndex_comap, hb]
  refine ⟨((perSub K κ ι D).relIndex (t 1) : ℝ) / (D : ℝ) ^ d, by positivity, fun φ hφ => ?_⟩
  obtain ⟨S, hS, hψ⟩ : IsSB (fun m => φ (e m)) :=
    Dict.isSB_comp e.toAddMonoidHom D D' hD hD' h1 (fun x hx => by simpa using h2 _ hx) hφ
  obtain ⟨R, hR, hφ⟩ := hφ
  obtain ⟨g, hg⟩ := transport e (perSub K' κ' ι' R) φ (periodic hφ)
  have hidx : (perSub K κ ι (R * D * S)).relIndex (t R) =
      S ^ d * (perSub K κ ι D).relIndex (t 1) := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (perSub_le (R * D) S) (hle R), hsc R hR,
      relIndex_perSub _ _ (by positivity)]
  have hfin : (Function.support fun q : Matrix κ ι K ⧸ t R => φ (e q.out)).Finite := by
    have := (finite_support hR hφ).preimage (f := g) g.injective.injOn
    refine this.subset fun q hq => ?_
    simp only [Set.mem_preimage, Function.mem_support] at hq ⊢
    rwa [← hg]
  have hsum := finsum_quotient_of_le ((perSub_le (R * D) S).trans (hle R))
    (by rw [hidx]; positivity) (fun m => φ (e m))
    (fun x y hy => by rw [map_add]; exact periodic hφ _ _ hy) hfin
  have hsum2 : ∑ᶠ q : Matrix κ ι K ⧸ t R, φ (e q.out) =
      ∑ᶠ q : Matrix κ' ι' K' ⧸ perSub K' κ' ι' R, φ q.out := by
    rw [← finsum_comp_equiv g]
    exact finsum_congr hg
  rw [(haar_eq_haarAt _ _ _ S _ hS hψ).1, (haar_eq_haarAt _ _ _ R _ hR hφ).1,
    ← haarAt_mul hS hψ (S := R * D) (by positivity), mul_comm S, haarAt, haarAt, hsum, hsum2, hidx,
    ← hd, ← hdd]
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hD'' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  rw [mul_pow, mul_pow]
  field_simp
end GlobalTheory.SW.HaarProp
