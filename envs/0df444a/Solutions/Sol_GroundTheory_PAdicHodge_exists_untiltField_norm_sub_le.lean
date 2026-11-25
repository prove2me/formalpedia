-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_untiltField_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:52:45.39315+00:00
-- url     : https://prove2.me/submissions/a225c5ba-b2f6-46c8-8005-fb358b692e0c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_eq_of_normedAlgebra
import Theorems.Thm_GroundTheory_PAdicHodge_coeff_monicOfCoeffs
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_mem_Ioc
import Theorems.Thm_GroundTheory_PAdicHodge_exists_root_norm_sub_untilt_pow_le
import Theorems.Thm_GroundTheory_PAdicHodge_map_scale_eq_prod
import Theorems.Thm_GroundTheory_PAdicHodge_monic_monicOfCoeffs
import Theorems.Thm_GroundTheory_PAdicHodge_norm_coeff_prod_X_sub_C_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_of_isConjRoot
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_tiltSharp_mem_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_untiltField_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
set_option synthInstance.maxHeartbeats 200000
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsAlgClosed C] [IsAlgClosed C♭]
    (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [FiniteDimensional K (untiltField K C p N)]
    (happrox : ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
      ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    {α : C} (hα : IsIntegral K α) {μ ε : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hμ : ‖(p : K)‖ ≤ μ ^ (minpoly K α).natDegree) (hε0 : 0 < ε) (hε1 : ε < 1)
    {β : C} (hβ : β ∈ untiltField K C p N) :
    ∃ N' : IntermediateField K♭ C♭, N ≤ N' ∧ FiniteDimensional K♭ N' ∧
      ∃ β' ∈ untiltField K C p N', ‖α - β'‖ ≤ μ / ε * ‖α - β‖ := by
  classical
  by_cases hαβ : α = β
  · exact ⟨N, le_rfl, inferInstance, β, hβ, by rw [hαβ, sub_self, norm_zero, mul_zero]⟩
  set F := untiltField K C p N with hFdef
  have hδ : 0 < ‖α - β‖ := norm_pos_iff.2 (sub_ne_zero.2 hαβ)
  have : CompleteSpace K := IsPerfectoidField.completeSpace p
  have : CompleteSpace F := FiniteDimensional.complete K F
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioc (K := K) p hδ
    (b := ‖α - β‖ / ε) (by rw [lt_div_iff₀ hε0]; nlinarith)
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [norm_zero] at hc1; linarith
  set c' : C := algebraMap K C c
  have hc'0 : c' ≠ 0 := (map_ne_zero_iff _ (algebraMap K C).injective).2 hc0
  have hnc' : ‖c'‖ = ‖c‖ := norm_algebraMap' C c
  have hαF : IsIntegral F α := hα.tower_top
  set Q := minpoly F α
  have hQm : Q.Monic := minpoly.monic hαF
  set e := Q.natDegree with hedef
  have he0 : 0 < e := minpoly.natDegree_pos hαF
  have hed : e ≤ (minpoly K α).natDegree := by
    have hdvd : Q ∣ (minpoly K α).map (algebraMap K F) :=
      minpoly.dvd_map_of_isScalarTower K F α
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.map_ne_zero (minpoly.ne_zero hα))
    rwa [natDegree_map] at this
  set βF : F := ⟨β, hβ⟩
  set cF : F := algebraMap K F c
  have hcF : cF ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).2 hc0
  set Qt : F[X] := Polynomial.C (cF⁻¹ ^ e) * Q.comp (Polynomial.C βF + Polynomial.C cF * X)
  set R := (Q.map (algebraMap F C)).roots
  have hQt : Qt.map (algebraMap F C) = (R.map fun γ => X - Polynomial.C ((γ - β) / c')).prod :=
    map_scale_eq_prod (E := C) hQm βF cF hcF

  have hQne : Q.map (algebraMap F C) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hαF)
  have hαR : α ∈ R := by
    rw [mem_roots hQne, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval F α
  have hdist : ∀ γ ∈ R, ‖γ - β‖ = ‖α - β‖ := by
    intro γ hγ
    have hγ' : aeval γ Q = 0 := by
      have := (mem_roots hQne).1 hγ
      rwa [IsRoot, eval_map_algebraMap] at this
    have hconj : IsConjRoot F α γ :=
      (isConjRoot_iff_mem_minpoly_rootSet hαF).2 (mem_rootSet.2 ⟨minpoly.ne_zero hαF, hγ'⟩)
    have := norm_eq_of_isConjRoot (F := F) (E := C) (hαF.sub isIntegral_algebraMap)
      (hconj.sub_algebraMap βF)
    exact this.symm
  have hrootle : ∀ r ∈ R.map (fun γ => (γ - β) / c'), ‖r‖ ≤ 1 := by
    intro r hr
    obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.1 hr
    rw [norm_div, hdist γ hγ, hnc']
    exact div_le_one_of_le₀ hc1.le (norm_nonneg _)
  set Qt' := Qt.map (algebraMap F C) with hQt'def
  have hQt' : Qt' = ((R.map (fun γ => (γ - β) / c')).map fun r => X - Polynomial.C r).prod := by
    rw [hQt, Multiset.map_map]; rfl
  have hcoef : ∀ n, ‖Qt'.coeff n‖ ≤ 1 := fun n => by
    rw [hQt']; exact norm_coeff_prod_X_sub_C_le_one hrootle n
  have hcard : Multiset.card R = e := by
    rw [← (IsAlgClosed.splits (Q.map (algebraMap F C))).natDegree_eq_card_roots, natDegree_map]
  have hQt'deg : Qt'.natDegree = e := by
    rw [hQt', natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, hcard]
  have hQt'mon : Qt'.Monic := by
    rw [hQt']; exact monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r

  have hsub : (↑Qt'.coeffs : Set C) ⊆ normInteger C := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
    exact mem_normInteger.2 (hcoef n)
  set Qi := Qt'.toSubring (normInteger C) hsub
  have hQi : Qi.map (normInteger C).subtype = Qt' := Polynomial.map_toSubring _ _ hsub
  have hQimon : Qi.Monic := by
    refine Polynomial.monic_of_injective (normInteger C).subtype_injective ?_
    rw [hQi]; exact hQt'mon
  have hQideg : Qi.natDegree = e := by
    rw [← hQt'deg, ← hQi, natDegree_map_eq_of_injective (normInteger C).subtype_injective]
  have hz1 : ‖(α - β) / c'‖ ≤ 1 :=
    hrootle _ (Multiset.mem_map.2 ⟨α, hαR, rfl⟩)
  set z : normInteger C := ⟨(α - β) / c', mem_normInteger.2 hz1⟩
  have hz : Qi.eval z = 0 := by
    apply (normInteger C).subtype_injective
    rw [map_zero, ← eval₂_at_apply, ← eval_map, hQi, hQt, eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map.2 ⟨α, hαR, rfl⟩, ?_⟩)
    simp [z]

  have happ : ∀ m, ∃ a : 𝒪C♭, m < e → a ∈ integerTilt K C p N ∧
      Ideal.Quotient.mk (Ideal.span {(p : normInteger C)}) (Qi.coeff m) = PreTilt.coeff 0 a := by
    intro m
    by_cases hm : m < e
    · have hy : ((Qt.coeff m : F) : C) ∈ F := (Qt.coeff m).2
      have hy1 : ‖((Qt.coeff m : F) : C)‖ ≤ 1 := by
        have := hcoef m
        rwa [hQt'def, coeff_map] at this
      obtain ⟨a, ha, hab⟩ := happrox _ hy hy1
      refine ⟨a, fun _ => ⟨ha, ?_⟩⟩
      rw [← PreTilt.mk_untilt_eq_coeff_zero, mk_eq_mk_iff_norm_sub_le,
        norm_natCast_eq_of_normedAlgebra (K := K)]
      have : ((Qi.coeff m : normInteger C) : C) = ((Qt.coeff m : F) : C) := by
        rw [← (normInteger C).subtype_apply, ← coeff_map, hQi, hQt'def, coeff_map]; rfl
      rw [this]; exact hab
    · exact ⟨0, fun h => absurd h hm⟩
  choose a ha using happ
  have hdeg : 0 < Qi.natDegree := hQideg ▸ he0
  obtain ⟨b, hbroot, hbnorm⟩ := exists_root_norm_sub_untilt_pow_le (C := C) (p := p) hQimon hdeg a
    (fun m hm => (ha m (hQideg ▸ hm)).2) hz
  rw [hQideg] at hbnorm hbroot

  have hbμ : ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ≤ μ := by
    have h1 : ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ^ e ≤ μ ^ e := by
      refine hbnorm.trans ?_
      rw [norm_natCast_eq_of_normedAlgebra (K := K)]
      exact hμ.trans (pow_le_pow_of_le_one hμ0 hμ1 hed)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hμ0 he0.ne').1 h1

  set b' : C♭ := algebraMap 𝒪C♭ C♭ b
  set g : C♭[X] := (monicOfCoeffs e a).map (algebraMap 𝒪C♭ C♭)
  have hgmon : g.Monic := (monic_monicOfCoeffs e a).map _
  have hgmem : ∀ n, g.coeff n ∈ N := by
    intro n
    rw [coeff_map, coeff_monicOfCoeffs]
    split_ifs with h1 h2
    · rw [map_one]; exact one_mem N
    · exact (ha n h2).1
    · rw [map_zero]; exact zero_mem N
  have hlift : g ∈ Polynomial.lifts (algebraMap N C♭) :=
    (lifts_iff_coeff_lifts g).2 fun n => ⟨⟨g.coeff n, hgmem n⟩, rfl⟩
  obtain ⟨gN, hgN, -, hgNmon⟩ := lifts_and_natDegree_eq_and_monic hlift hgmon
  have hbN : IsIntegral N b' := by
    refine ⟨gN, hgNmon, ?_⟩
    rw [← eval_map, hgN, eval_map, eval₂_at_apply, hbroot, map_zero]
  have hbK : IsIntegral K♭ b' := isIntegral_trans b' hbN
  have : FiniteDimensional K♭ (IntermediateField.adjoin K♭ {b'}) :=
    IntermediateField.adjoin.finiteDimensional hbK
  set N' := N ⊔ IntermediateField.adjoin K♭ {b'}
  have hb'N' : b' ∈ N' :=
    (le_sup_right : IntermediateField.adjoin K♭ {b'} ≤ N')
      (IntermediateField.mem_adjoin_simple_self K♭ b')
  refine ⟨N', le_sup_left, inferInstance, β + c' * ((PreTilt.untilt b : normInteger C) : C), ?_, ?_⟩
  · refine add_mem (untiltField_mono le_sup_left hβ) (mul_mem ?_ ?_)
    · exact IntermediateField.algebraMap_mem _ c
    · have := tiltSharp_mem_untiltField (K := K) (N := N') hb'N'
      rwa [tiltSharp_algebraMap] at this
  · have hsplit : α - (β + c' * ((PreTilt.untilt b : normInteger C) : C)) =
        c' * ((z : C) - ((PreTilt.untilt b : normInteger C) : C)) := by
      simp only [z]; field_simp; ring
    rw [hsplit, norm_mul, hnc']
    calc ‖c‖ * ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ≤ ‖α - β‖ / ε * μ := by
          gcongr
      _ = μ / ε * ‖α - β‖ := by ring
end GroundTheory.PAdicHodge
