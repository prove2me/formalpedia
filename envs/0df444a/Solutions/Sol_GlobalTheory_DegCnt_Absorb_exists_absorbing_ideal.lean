-- Prove2me | solution 1 for GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:32:20.445796+00:00
-- url     : https://prove2.me/submissions/9d57735f-6e2b-4d64-a44b-f9a22a146017

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_nat
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_exists_ideal
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SgLoc_PtAlg_isUnit_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
namespace GlobalTheory.DegCnt.Absorb
section Ideals
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K]
end Ideals
section Flags
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem exists_mem_pow_eq_star (N : _root_.GlobalTheory.DegCnt.NF H r) (k : ℕ) {d : 𝓞 K}
    (hd : d ∈ N.𝔡 ^ k) : ∃ d' ∈ N.𝔡 ^ k, (d' : K) = star (d : K) := by
  have h1 : N.𝔡 ≤ N.𝔡.comap (_root_.GlobalTheory.DegCnt.Absorb.sig K : 𝓞 K →+* 𝓞 K) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := N.𝔡_star x hx
    have : (_root_.GlobalTheory.DegCnt.Absorb.sig K x : 𝓞 K) = y := by
      ext; exact hyx.symm
    rw [Ideal.mem_comap]
    simpa [this] using hy
  have h2 := (Ideal.pow_right_mono h1 k).trans (Ideal.le_comap_pow _ k) hd
  exact ⟨_, h2, rfl⟩
end Flags
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
private theorem absNorm_map_sig_eq (A : Ideal (𝓞 K)) :
    Ideal.absNorm (A.map (_root_.GlobalTheory.DegCnt.Absorb.sig K)) = Ideal.absNorm A := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv A _ (_root_.GlobalTheory.DegCnt.Absorb.sig K) rfl).toEquiv.symm
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
private theorem coe_sig_eq_star (x : 𝓞 K) :
    ((_root_.GlobalTheory.DegCnt.Absorb.sig K x : 𝓞 K) : K) = star (x : K) := rfl
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
private theorem sig_mem_mul_of_sig_mem {I J : Ideal (𝓞 K)}
    (hI : ∀ x ∈ I, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I)
    (hJ : ∀ x ∈ J, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ J) :
    ∀ x ∈ I * J, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I * J := by
  intro x hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul]; exact Ideal.mul_mem_mul (hI a ha) (hJ b hb)
  · rw [map_add]; exact add_mem ha hb
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
private theorem sig_mem_prod_of_sig_mem (s : Finset ℕ) (I : ℕ → Ideal (𝓞 K))
    (h : ∀ l ∈ s, ∀ x ∈ I l, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I l) :
    ∀ x ∈ ∏ l ∈ s, I l, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ ∏ l ∈ s, I l := by
  induction s using Finset.cons_induction with
  | empty => intro x _; simp [Ideal.one_eq_top]
  | cons a s ha ih =>
    rw [Finset.prod_cons]
    have h1 : ∀ x ∈ I a, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I a := h a (Finset.mem_cons_self a s)
    have h2 := ih fun l hl => h l (Finset.mem_cons_of_mem hl)
    exact sig_mem_mul_of_sig_mem h1 h2
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
private theorem sig_sig_eq (x : 𝓞 K) :
    _root_.GlobalTheory.DegCnt.Absorb.sig K (_root_.GlobalTheory.DegCnt.Absorb.sig K x) = x := by
  ext
  show star (star (x : K)) = x
  exact star_star _
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
private theorem sig_mem_mul_map_sig (A : Ideal (𝓞 K)) :
    ∀ x ∈ A * A.map (_root_.GlobalTheory.DegCnt.Absorb.sig K),
      _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ A * A.map (_root_.GlobalTheory.DegCnt.Absorb.sig K) := by
  intro x hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_of_equiv _ _).1 hb
    rw [map_mul, sig_sig_eq, mul_comm ((_root_.GlobalTheory.DegCnt.Absorb.sig K) a) c]
    exact Ideal.mul_mem_mul hc (Ideal.mem_map_of_mem _ ha)
  · rw [map_add]; exact add_mem ha hb
end GlobalTheory.DegCnt.Absorb
end
end

set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Absorb
open NumberField
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegCnt.Absorb
namespace _root_.GlobalTheory.DegCnt.Absorb
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : _root_.GlobalTheory.DegCnt.NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔠 : Ideal (𝓞 K), (Ideal.absNorm 𝔠 : ℝ) ≤ (N.Db * N.NT) ^ 2 ∧ 1 ≤ N.Db ∧ 1 ≤ N.Del ∧ ∀ Q : Prop, (𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (_root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → Q) → Q := by
  intro K V _ _ _ _ _ _ _ _ H hCM r N g Λ _ hΛ
  haveI : IsTotallyComplex K := hCM.1
  have hF := hΛ.1
  choose A hA0 hA using fun l => _root_.GlobalTheory.DegCnt.Absorb.exists_ideal N hF l
  set S := (Finset.Icc 1 N.j).filter (fun l => N.nD l ≠ 0) with hSdef
  have hjr := N.j_le
  have hDne : ∀ l (hl : l ≤ r + 1), N.nD l ≠ 0 → _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 := by
    intro l hl hn hD
    apply hn
    unfold _root_.GlobalTheory.DegCnt.NF.nD
    rw [dif_pos hl, hD]
    simp
  have hS : ∀ l ∈ S, ∃ hl : l ≤ r + 1, l ≤ N.j ∧ _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 := by
    intro l hl
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hl
    have hl' : l ≤ r + 1 := by omega
    exact ⟨hl', hl.1.2, hDne l hl' hl.2⟩
  have hnorm : ∀ l ∈ S, (Ideal.absNorm (A l) : ℝ) = N.nD l := by
    intro l hl
    obtain ⟨hl', hlj, hD⟩ := hS l hl
    exact ((hA l) hl' hlj hD).1
  have hge : ∀ l ∈ S, 1 ≤ N.nD l := by
    intro l hl
    rw [← hnorm l hl]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 (hA0 l))
  have hT : (N.T : K) ≠ 0 := by
    rw [← N.hT]; exact N.F.hT
  have hT' : (N.T : 𝓞 K) ≠ 0 := by
    intro h0; apply hT; exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) h0
  refine ⟨Ideal.span {(N.T : 𝓞 K)} * ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)), ?_, ?_, ?_, fun Q hQ => hQ ?_ ?_ ?_ ?_⟩
  · have hsplit : (Ideal.absNorm (Ideal.span {(N.T : 𝓞 K)} * ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K))) : ℝ) =
        (N.T : ℝ) ^ Module.finrank ℚ K * ∏ l ∈ S, N.nD l ^ 2 := by
      rw [map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
      congr 1
      · rw [Ideal.absNorm_span_singleton,
          show (N.T : 𝓞 K) = algebraMap ℤ (𝓞 K) (N.T : ℤ) by simp, Algebra.norm_algebraMap,
          RingOfIntegers.rank]
        simp
      · refine Finset.prod_congr rfl fun l hl => ?_
        rw [map_mul, absNorm_map_sig_eq, Nat.cast_mul, hnorm l hl, sq]
    rw [hsplit]
    unfold _root_.GlobalTheory.DegCnt.NF.Db
      _root_.GlobalTheory.DegCnt.NF.NT _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add, mul_pow, ← Finset.prod_pow, ← pow_mul]
    apply le_of_eq
    ring
  · unfold _root_.GlobalTheory.DegCnt.NF.Db
    calc (1 : ℝ) = ∏ l ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) hge
  · unfold _root_.GlobalTheory.DegCnt.NF.Del
    have hj : N.j ≤ r + 1 := by omega
    have hDj : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' N.j hj ≠ 0 := by
      unfold _root_.Formalism.HermitianLatticeCounting.S6.Dl
      have hm : (_root_.Formalism.HermitianLatticeCounting.S6.Zhat N.F N.F').submatrix (Fin.castLE hj) (Fin.castLE hj) =
          N.w.mat *
            Matrix.diagonal (fun b => ((N.sgn b : ℤ) : K)) := by
        ext a b
        simp [_root_.Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.mul_diagonal, N.pair]
      rw [hm, Matrix.det_mul, Matrix.det_diagonal]
      refine mul_ne_zero (_root_.GlobalTheory.SgLoc.PtAlg.isUnit_det N.w).ne_zero
        (Finset.prod_ne_zero_iff.2 fun b _ => ?_)
      rcases Int.units_eq_one_or (N.sgn b) with h | h <;> simp [h]
    rw [← (hA N.j hj le_rfl hDj).1]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 (hA0 _))
  · rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨by rwa [Ideal.span_singleton_eq_bot], ?_⟩
    rw [← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff, not_exists]
    rintro l ⟨_, hl⟩
    rw [Ideal.zero_eq_bot, Ideal.mul_eq_bot] at hl
    rcases hl with h | h
    · exact hA0 l h
    · exact hA0 l (by rwa [Ideal.map_eq_bot_iff_of_injective (_root_.GlobalTheory.DegCnt.Absorb.sig K).injective] at h)
  · intro x hx
    refine ⟨_root_.GlobalTheory.DegCnt.Absorb.sig K x, ?_, coe_sig_eq_star x⟩
    have hstab : ∀ z ∈ ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)),
        _root_.GlobalTheory.DegCnt.Absorb.sig K z ∈ ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)) :=
      sig_mem_prod_of_sig_mem S (fun l => A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K))
        (fun l _ => sig_mem_mul_map_sig (A l))
    have hspan : ∀ z ∈ Ideal.span {(N.T : 𝓞 K)},
        _root_.GlobalTheory.DegCnt.Absorb.sig K z ∈ Ideal.span {(N.T : 𝓞 K)} := by
      intro y hy
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      rw [map_mul, map_natCast]
      exact Ideal.mem_span_singleton.2 (dvd_mul_left _ _)
    exact sig_mem_mul_of_sig_mem hspan hstab x hx
  · intro x hx
    have h1 : Ideal.span {(N.T : 𝓞 K)} *
        ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)) ≤
          Ideal.span {(N.T : 𝓞 K)} := Ideal.mul_le_left
    exact Ideal.mem_span_singleton.1 (h1 hx)
  · intro l hl hlj hD x hx y hy
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · have hD0 : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' 0 hl = 1 := by
        unfold _root_.Formalism.HermitianLatticeCounting.S6.Dl
        exact Matrix.det_isEmpty
      rw [hD0, star_one, div_one]
      have hy' : y ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 ((0 : ℕ) : ℤ) := by simpa using hy
      obtain ⟨d, _, rfl⟩ := (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hy'
      exact ⟨Submodule.mem_one.2 ⟨x * d, by simp⟩, Submodule.mem_one.2 ⟨x * d, by simp⟩⟩
    · have hlS : l ∈ S := by
        rw [hSdef, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hl0, hlj⟩, ?_⟩
        rw [← (hA l hl hlj hD).1]
        exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 (hA0 l)
      have hxl : x ∈ A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K) := by
        have h1 := Ideal.mul_le_right hx
        rw [← Finset.mul_prod_erase S _ hlS] at h1
        exact Ideal.mul_le_left h1
      refine ⟨(hA l hl hlj hD).2 x (Ideal.mul_le_left hxl) y hy, ?_⟩
      obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_of_equiv (_root_.GlobalTheory.DegCnt.Absorb.sig K) x).1 (Ideal.mul_le_right hxl)
      have he : 0 ≤ 2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a) := by
        refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun b hb => ?_)
        have := Finset.mem_range.1 hb
        omega
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le he
      rw [hk] at hy
      obtain ⟨d, hd, rfl⟩ := (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hy
      obtain ⟨d', hd', hdd'⟩ := exists_mem_pow_eq_star N k hd
      have h2 := (hA l hl hlj hD).2 a ha d'
        (by rw [hk]; exact (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).2 ⟨d', hd', rfl⟩)
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 h2
      refine Submodule.mem_one.2 ⟨_root_.GlobalTheory.DegCnt.Absorb.sig K o, ?_⟩
      have e1 : algebraMap (𝓞 K) K (_root_.GlobalTheory.DegCnt.Absorb.sig K o) =
          star (algebraMap (𝓞 K) K o) := coe_sig_eq_star o
      have e2 := coe_sig_eq_star a
      rw [e1, ho, e2, hdd', star_div₀, star_mul', star_star]
end _root_.GlobalTheory.DegCnt.Absorb
end GlobalTheory.DegCnt.Absorb
