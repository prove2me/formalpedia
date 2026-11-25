-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.exists_almostNorm_etaProd_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:58.949961+00:00
-- url     : https://prove2.me/submissions/afdc497b-2fe9-41a9-88f4-82b03d0e3a3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceNotIsSquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAlmostNormEtaProdEqNegOne
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_finrank_eq_two
import Theorems.Thm_GlobalTheory_QNorm_exists_admissible_superset_finite_places
import Theorems.Thm_GlobalTheory_QNorm_exists_local_nonnorm
import Theorems.Thm_GlobalTheory_QNorm_exists_superset_mem_sUnits
import Theorems.Thm_GlobalTheory_QNorm_mem_normSub
import Theorems.Thm_GlobalTheory_QNorm_sUnits_sup_locNorm_ne_top
import Theorems.Thm_GlobalTheory_QNorm_two_pow_le_index_locNorm
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_neg_one_iff
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_one_iff
import Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff_form
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


section
open NumberField IsDedekindDomain
namespace GlobalTheory.QuadSymbol
open NumberField IsDedekindDomain in
private theorem linearIndependent_one_of_notMem_range {K L : Type} [Field K] [Field L] [Algebra K L]
    {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) : LinearIndependent K ![(1 : L), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · subst ht
    simp only [map_zero, zero_mul, add_zero, map_eq_zero] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply hθ
    refine ⟨-s / t, ?_⟩
    have ht' : algebraMap K L t ≠ 0 := (map_ne_zero _).mpr ht
    rw [map_div₀, map_neg, div_eq_iff ht']
    linear_combination -hst
open NumberField IsDedekindDomain in
private theorem exists_basis_one_sqrt_nonsquare_of_finrank_two (K L : Type) [Field K] [CharZero K] [Field L]
    [Algebra K L] (h2 : Module.finrank K L = 2) :
    ∃ (e : Module.Basis (Fin 2) K L) (δ : K), e 0 = 1 ∧ e 1 * e 1 = algebraMap K L δ ∧
      ¬ IsSquare δ := by
  obtain ⟨θ, hθ⟩ : ∃ θ : L, θ ∉ Set.range (algebraMap K L) := by
    by_contra hcon
    push_neg at hcon
    have hbot : (⊥ : Subalgebra K L) = ⊤ :=
      eq_top_iff.mpr fun x _ => Algebra.mem_bot.mpr (hcon x)
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
    omega
  let B := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_notMem_range hθ)
    (by simp [h2])
  have hB : ∀ i, B i = ![(1 : L), θ] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hθθ : θ * θ = algebraMap K L (B.repr (θ * θ) 0) +
      algebraMap K L (B.repr (θ * θ) 1) * θ := by
    conv_lhs => rw [← B.sum_repr (θ * θ)]
    rw [Fin.sum_univ_two, hB, hB, Algebra.smul_def, Algebra.smul_def]
    simp
  set q := B.repr (θ * θ) 0
  set p := B.repr (θ * θ) 1
  clear_value p q
  have hθ' : θ - algebraMap K L (p / 2) ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    exact hθ ⟨c + p / 2, by rw [map_add, hc]; ring⟩
  have hp2 : algebraMap K L (p / 2) * 2 = algebraMap K L p := by
    rw [← map_ofNat (algebraMap K L) 2, ← map_mul, div_mul_cancel₀ p two_ne_zero]
  have hδeq : algebraMap K L (q + p ^ 2 / 4) = algebraMap K L q + algebraMap K L (p / 2) ^ 2 := by
    rw [show q + p ^ 2 / 4 = q + (p / 2) ^ 2 by ring, map_add, map_pow]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_notMem_range hθ')
    (by simp [h2]), q + p ^ 2 / 4, ?_, ?_, ?_⟩
  · simp [coe_basisOfLinearIndependentOfCardEqFinrank]
  · simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [hδeq]
    linear_combination hθθ - θ * hp2
  · rintro ⟨c, hc⟩
    have hsq : (θ - algebraMap K L (p / 2) - algebraMap K L c) *
        (θ - algebraMap K L (p / 2) + algebraMap K L c) = 0 := by
      have hc' := congrArg (algebraMap K L) hc
      rw [hδeq, map_mul] at hc'
      linear_combination hθθ - θ * hp2 + hc'
    rcases mul_eq_zero.mp hsq with h | h
    · exact hθ' ⟨c, by linear_combination -h⟩
    · exact hθ' ⟨-c, by rw [map_neg]; linear_combination -h⟩
open NumberField IsDedekindDomain in
private theorem exists_sq_sub_mul_sq_of_isSquare {K : Type} [Field K] [CharZero K] {d : K}
    (hd : d ≠ 0) (hsq : IsSquare d) (x : K) : ∃ a b : K, x = a ^ 2 - d * b ^ 2 := by
  obtain ⟨c, rfl⟩ := hsq
  have hc : c ≠ 0 := by rintro rfl; simp at hd
  refine ⟨(x + 1) / 2, (x - 1) / (2 * c), ?_⟩
  field_simp
  ring
open NumberField IsDedekindDomain in
private theorem exists_place_notMem_not_isSquare (F : Type) [Field F] [NumberField F] (δ : F)
    (hδ0 : δ ≠ 0) (hδ : ¬ IsSquare δ) (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ) := by
  classical
  by_contra hcon
  push_neg at hcon
  set d : Fˣ := Units.mk0 δ hδ0 with hd
  have hidx := (_root_.GlobalTheory.QNorm.two_pow_le_index_locNorm F δ S₀ hδ0).1
  haveI : (_root_.GlobalTheory.QNorm.locNorm F δ S₀).FiniteIndex := ⟨hidx⟩
  haveI := Fintype.ofFinite (Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀)
  let X : Finset Fˣ := insert d
    (Finset.univ.image fun q : Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀ => q.out)
  obtain ⟨S₁, -, hS₁⟩ := _root_.GlobalTheory.QNorm.exists_superset_mem_sUnits F X S₀
  obtain ⟨S, hS₁S, hadm⟩ := _root_.GlobalTheory.QNorm.exists_admissible_superset_finite_places F (S₁ ∪ S₀)
  have hmem : ∀ x ∈ X, x ∈ _root_.GlobalTheory.QNorm.sUnits F S :=
    hS₁ S (Finset.union_subset_left hS₁S)
  have hdδ : (d : F) = δ := rfl
  refine _root_.GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top F d S hadm (hmem d (Finset.mem_insert_self _ _))
    (by rwa [hdδ]) ?_
  have hle : _root_.GlobalTheory.QNorm.locNorm F δ S₀ ≤ _root_.GlobalTheory.QNorm.locNorm F (d : F) S := by
    intro x hx
    rw [hdδ]
    unfold _root_.GlobalTheory.QNorm.locNorm at hx ⊢
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hx ⊢
    refine ⟨fun v hv => ?_, hx.2⟩
    by_cases hv0 : v ∈ S₀
    · exact hx.1 v hv0
    · rw [_root_.GlobalTheory.QNorm.mem_normSub]
      haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F _).injective
      exact exists_sq_sub_mul_sq_of_isSquare ((map_ne_zero _).mpr hδ0) (hcon v hv0) _
  rw [eq_top_iff]
  intro t _
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.QNorm.locNorm F δ S₀) t
  have ht : t = (QuotientGroup.mk t : Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀).out * (h : Fˣ)⁻¹ := by
    rw [hh]; group
  rw [ht]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hmem _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))
    (Subgroup.mem_sup_right (hle (Subgroup.inv_mem _ h.2)))
end GlobalTheory.QuadSymbol
end

set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QuadSymbol
open NumberField IsDedekindDomain
namespace GlobalTheory.QuadSymbol
namespace _root_.GlobalTheory.QuadSymbol
theorem _root_.solution :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L],
      ∃ (x : _root_.GlobalTheory.QuadSymbol.FinFam K) (y : _root_.GlobalTheory.QuadSymbol.InfFam K),
        _root_.GlobalTheory.QuadSymbol.AlmostNorm K L x ∧ _root_.GlobalTheory.QuadSymbol.etaProd K L x y = -1 := by
  intro K L _ _ _ _ _ _
  classical
  obtain ⟨e, δ, he0, he1, hδ⟩ := exists_basis_one_sqrt_nonsquare_of_finrank_two K L
    (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ ⟨0, by simp⟩
  obtain ⟨v, -, hv⟩ := exists_place_notMem_not_isSquare K δ hδ0 hδ ∅
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.QNorm.exists_local_nonnorm K v _
    ((map_ne_zero _).mpr hδ0) hv
  have hnot : Units.mk0 x hx0 ∉ _root_.GlobalTheory.QuadSymbol.normGroup K L (v.adicCompletion K) := by
    rw [_root_.GlobalTheory.QuadSymbol.mem_normGroup_iff_form e he0 he1]
    exact hx
  refine ⟨Pi.mulSingle v (Units.mk0 x hx0), 1, ?_, ?_⟩
  · unfold _root_.GlobalTheory.QuadSymbol.AlmostNorm
    refine (Set.finite_singleton v).subset fun v' hv' => ?_
    by_contra hne
    apply hv'
    rw [Pi.mulSingle_eq_of_ne (Set.mem_singleton_iff.not.mp hne)]
    exact Subgroup.one_mem _
  · unfold _root_.GlobalTheory.QuadSymbol.etaProd
    rw [finprod_eq_single _ v]
    · rw [Pi.mulSingle_eq_same, _root_.GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.mpr hnot,
        Finset.prod_eq_one, mul_one]
      intro w _
      exact _root_.GlobalTheory.QuadSymbol.eta_eq_one_iff.mpr (Subgroup.one_mem _)
    · intro v' hv'
      rw [Pi.mulSingle_eq_of_ne hv']
      exact _root_.GlobalTheory.QuadSymbol.eta_eq_one_iff.mpr (Subgroup.one_mem _)
end _root_.GlobalTheory.QuadSymbol
end GlobalTheory.QuadSymbol
