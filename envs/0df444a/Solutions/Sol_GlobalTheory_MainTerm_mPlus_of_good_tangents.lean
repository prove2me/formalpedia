-- Prove2me | solution 1 for GlobalTheory.MainTerm.mPlus_of_good_tangents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:04:25.420368+00:00
-- url     : https://prove2.me/submissions/35c04067-e578-4502-8849-45044267b1fc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearSubstCoordinateIntegralOfDegreeLtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HPullWUpGTwoGroupEmbeddingEqRenameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeSubMainTermIntegralLowBidegree
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_l_ne_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_inv_unit_int
import Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_sum
import Theorems.Thm_GlobalTheory_MainTerm_tan_pure
import Theorems.Thm_GlobalTheory_T_coeffIntegralOnExponents_subst_of_lower_set
import Theorems.Thm_GlobalTheory_T_coeff_coordinates_good_tangents_lt_sq
import Theorems.Thm_GlobalTheory_T_coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis
import Theorems.Thm_GlobalTheory_T_hPullW_upG_twoGroupEmbedding_eq_rename
import Theorems.Thm_GlobalTheory_T_linearSubst_coordinate_integral_of_degree_lt
import Theorems.Thm_GlobalTheory_T_pderiv_leafGauge_eq_pairing_add_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_natCast_eq_zero_of_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
namespace GlobalTheory.MainTerm
private theorem ge_coeff_rename_inl {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι →₀ ℕ, ν.degree = ∑ c, μ (Sum.inl c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inl F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply Sum.inl_injective]
private theorem ge_coeff_rename_inr {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι' C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι' →₀ ℕ, ν.degree = ∑ c, μ (Sum.inr c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inr F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply Sum.inr_injective]
private theorem constantCoeff_linPull_eq_zero {C : Type} [Field C] {σ ι : Type} [Fintype σ]
    [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C)
    (h : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (linPull e F) = 0 := by
  unfold linPull
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  · intro x
    simp
  · exact h
private theorem pderiv_inr_mainM_one {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (Φ : ι' → ι → C) (b : ι') :
    MvPowerSeries.pderiv C (Sum.inr b) (mainM V 1 Φ) =
      MvPowerSeries.rename Sum.inl ((V.l : C)⁻¹ • ∑ c : ι,
        Φ b c • (MvPowerSeries.X c : MvPowerSeries ι C) ^ V.l) := by
  have hE : expE V.l 1 = 1 := by simp [expE]
  unfold mainM
  rw [hE, pow_one, pow_one]
  simp only [map_smul, map_sum, MvPowerSeries.rename_X, map_pow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_eq_single b]
  · rw [Derivation.map_smul, Derivation.leibniz, MvPowerSeries.pderiv_X_self, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr]
    simp [mul_comm]
  · intro x _ hx
    rw [Derivation.map_smul, Derivation.leibniz, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr,
      MvPowerSeries.pderiv_X_of_ne (fun h => hx (Sum.inr_injective h))]
    simp
  · intro hb
    exact absurd (Finset.mem_univ b) hb
end GlobalTheory.MainTerm
end

set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.MainTerm
namespace GlobalTheory.MainTerm
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 1 < d → ∀ (g : Fin 2) (a : ZMod d) (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N : ℕ) (em : Fin N ↪ I g) (v' : Fin X.n → I (1 - g) → C), (∀ δ, (X.G g).ty (Sum.inl (em δ)) = a) → (∀ δ x, (S g).al (em δ) 1 x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + ((1 : ℕ) : ZMod d) → v' b k = 0) → X.MPlusConcl g a N (fun δ => (S g).tan (em δ)) v' (fun b c => ∑ κ : J g, ∑ k : I (1 - g), -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k) := by
  intro C _ V d _ I J _ _ X hAlt hd g a S t hT N em v' hty hal hint hpure μ hμl hμr
  by_cases h0 : ∀ b, μ (Sum.inr b) = 0
  · rw [GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis _ _ _ _ _ X g a 1 _ _ _ v' _ μ h0]
    exact VF.Ge.zero 0
  simp only [not_forall] at h0
  obtain ⟨b, hb⟩ := h0
  have he_pure : ∀ (c : Fin N) (x : I g), (X.G g).ty (Sum.inl x) ≠ a →
      (fun δ => (S g).tan (em δ)) c x = 0 := by
    intro c x hx
    exact tan_pure (S g) (em c) x (by rw [hty c]; exact hx)
  obtain ⟨γ, hγ, hγeq⟩ := GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral C V d I J X hAlt g a 1 odd_one hd S t hT (Fin N) (Fin X.n)
    (fun δ => (S g).tan (em δ)) v' he_pure hint hpure b
  have h91 := GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename C I g (Fin N) (Fin X.n) (fun δ => (S g).tan (em δ)) v'
  have hsingle : Finsupp.single (Sum.inr b) 1 ≤ μ :=
    Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hb)
  obtain ⟨μ', rfl⟩ : ∃ μ', μ = μ' + Finsupp.single (Sum.inr b) 1 :=
    ⟨μ - Finsupp.single (Sum.inr b) 1, (tsub_add_cancel_of_le hsingle).symm⟩
  have hl' : ∑ c, μ' (Sum.inl c) < V.l ^ 2 :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμl
  have hr' : ∑ b', μ' (Sum.inr b') < V.l :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμr
  have hbl : μ' (Sum.inr b) + 1 < V.l := by
    refine lt_of_le_of_lt ?_ hμr
    have := Finset.single_le_sum (f := fun b' => (μ' + Finsupp.single (Sum.inr b) 1 : Fin N ⊕ Fin X.n →₀ ℕ) (Sum.inr b'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using this
  have hunit : V.v ((μ' (Sum.inr b) : C) + 1) = 0 := by
    have hc : ((μ' (Sum.inr b) : C) + 1) = ((μ' (Sum.inr b) + 1 : ℕ) : C) := by push_cast; ring
    rw [hc]
    exact ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_zero_of_coprime V.v V.v_l
      (Nat.coprime_of_lt_prime (by omega) hbl V.l_prime)
  have hne : ((μ' (Sum.inr b) : C) + 1) ≠ 0 := by
    intro h
    rw [h] at hunit
    simp at hunit
  set Φ : Fin X.n → Fin N → C := fun b c => ∑ κ : J g, ∑ k : I (1 - g),
    -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k with hΦ
  set F := X.hM g a 1 (fun δ => (S g).tan (em δ)) v' - mainM V 1 Φ with hF
  have hcoeff : MvPowerSeries.coeff (μ' + Finsupp.single (Sum.inr b) 1) F =
      ((μ' (Sum.inr b) : C) + 1)⁻¹ * MvPowerSeries.coeff μ' (MvPowerSeries.pderiv C (Sum.inr b) F) := by
    rw [MvPowerSeries.coeff_pderiv]
    field_simp
  rw [hcoeff]
  refine VF.Ge.mul_int (inv_unit_int hunit) ?_
  set G : MvPowerSeries (Fin N) C :=
    (∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • linPull (fun δ => (S g).tan (em δ)) ((S g).ze (t g) κ)) -
      (V.l : C)⁻¹ • ∑ c : Fin N, Φ b c • (MvPowerSeries.X c : MvPowerSeries (Fin N) C) ^ V.l with hG
  have hsplit : MvPowerSeries.pderiv C (Sum.inr b) F =
      MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2))
        (fun c => toW g ((fun δ => (S g).tan (em δ)) c)) (fun b => toW (1 - g) (v' b))) γ +
      MvPowerSeries.rename Sum.inl G := by
    rw [hF, map_sub, hγeq, pderiv_inr_mainM_one V Φ b]
    simp only [h91.1, hG, map_sub, map_sum, map_smul]
    abel
  rw [hsplit, map_add]
  refine VF.Ge.add ?_ ?_
  · have h2 : ∀ j g : Fin 2, j = g ∨ j = 1 - g := by decide
    refine GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set C V (Fin N ⊕ Fin X.n) (WV I)
      (fun ν => ∑ c, ν (Sum.inl c) < V.l ^ 2 ∧ ∑ b', ν (Sum.inr b') < V.l) ?_ γ _ hγ ?_ ?_ μ' ⟨hl', hr'⟩
    · intro ν ν' hle hP
      exact ⟨lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inl c)) hP.1,
        lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inr c)) hP.2⟩
    · rintro ⟨j, x⟩
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT j).1 x)
      · simp only
        rw [h91.2, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT (1 - g)).1 x)
    · rintro ⟨j, x⟩ ν hP
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1]
        apply ge_coeff_rename_inl V
        intro ν' hν'
        rw [(GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq C V d (I j) (J j) (X.G j) (S j) (t j) (hT j) N em hal ν'
          (by rw [hν']; exact hP.1)).1 x, map_sum]
        apply VF.Ge.sum
        intro δ _
        split_ifs
        · rw [MvPowerSeries.coeff_X]
          split_ifs
          exacts [VF.Ge.one, VF.Ge.zero 0]
        · rw [map_zero]
          exact VF.Ge.zero 0
      · simp only
        rw [h91.2]
        apply ge_coeff_rename_inr V
        intro ν' hν'
        exact GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt C V d (I (1 - g)) (J (1 - g)) (X.G (1 - g)) (S (1 - g)) (t (1 - g))
          (hT (1 - g)) X.n v' hint ν' (by rw [hν']; exact hP.2) x
  · apply ge_coeff_rename_inl V
    intro ν hν
    have hdeg : ν.degree < V.l ^ 2 := by rw [hν]; exact hl'
    have h19 := (GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq C V d (I g) (J g) (X.G g) (S g) (t g) (hT g) N em hal ν hdeg).2
    have hz : MvPowerSeries.coeff ν G = 0 := by
      rw [hG, map_sub, map_sum]
      simp only [MvPowerSeries.coeff_smul, h19, map_neg, map_sum, hΦ]
      have hL : (V.l : C) ≠ 0 := VF.l_ne_zero
      rw [sub_eq_zero]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib, neg_mul]
      rw [neg_inj, Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [hz]
    exact VF.Ge.zero 0
end GlobalTheory.MainTerm
