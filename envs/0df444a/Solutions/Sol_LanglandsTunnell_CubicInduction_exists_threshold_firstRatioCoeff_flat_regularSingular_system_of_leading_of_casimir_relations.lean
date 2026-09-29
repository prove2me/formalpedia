-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ecdd4cfa-42a9-544f-aee2-bf4d29059a89

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
import Theorems.Thm_RegularSingular_exists_logDepth_le_natDegree_norm_sub_expansion_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fin.Rev
import Theorems.Thm_RegularSingular_hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le
import Theorems.Thm_RegularSingular_exists_expansion_coeff_of_folded_system
import Theorems.Thm_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_joint_expansion_of_casimir_relations
import Theorems.Thm_RegularSingular_hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
import Theorems.Thm_RegularSingular_expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_and_sum_smul_iterate_casimir_eq_zero_of_mem_span_foldr_archDeriv_mul_right
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
import Theorems.Thm_LanglandsTunnell_CubicInduction_foldr_archDeriv_mul_right_eq_sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply"
p2m_attr_erase "simp" "IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul"

namespace A7Port

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.CubicInduction

theorem family_of_polys (q q' : Polynomial ℂ) (hq : q ≠ 0) (hq' : q' ≠ 0) (ρ : ℝ) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ ∧ Function.Injective e ∧ (∀ i, (e i).re ≤ ρ) ∧
      (∀ μ : ℂ, ((∃ e₀ : ℂ, q.IsRoot e₀ ∧ ∃ m : ℕ, μ = e₀ + m) ∨ (∃ e₀ : ℂ, q'.IsRoot e₀ ∧ ∃ m : ℕ, μ = e₀ + m)) →
        μ.re ≤ ρ → ∃ i, e i = μ) ∧
      (∀ e₀ : ℂ, q.IsRoot e₀ → ∀ m : ℕ, ρ < (e₀ + m).re → ρ + 2 * δ ≤ (e₀ + m).re) ∧
      (∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ m : ℕ, ρ < (e₀ + m).re → ρ + 2 * δ ≤ (e₀ + m).re) ∧
      (∀ i, ∃ e₀ : ℂ, (q.IsRoot e₀ ∨ q'.IsRoot e₀) ∧ ∃ m : ℕ, e i = e₀ + m) := by
  classical

  set R : Finset ℂ := q.roots.toFinset ∪ q'.roots.toFinset with hR
  have hmemR : ∀ e₀ : ℂ, (q.IsRoot e₀ ∨ q'.IsRoot e₀) → e₀ ∈ R := by
    intro e₀ h
    rcases h with h | h
    · exact Finset.mem_union_left _ ((Multiset.mem_toFinset).2 ((Polynomial.mem_roots hq).2 h))
    · exact Finset.mem_union_right _ ((Multiset.mem_toFinset).2 ((Polynomial.mem_roots hq').2 h))

  set B : ℕ := ⌈ρ⌉₊ + R.sup (fun e₀ => ⌈|e₀.re|⌉₊) with hB
  have hre_add : ∀ (e₀ : ℂ) (m : ℕ), (e₀ + (m : ℂ)).re = e₀.re + m := by
    intro e₀ m; simp
  have hceil : ∀ e₀ ∈ R, ρ - e₀.re ≤ (⌈ρ⌉₊ : ℝ) + (⌈|e₀.re|⌉₊ : ℝ) := by
    intro e₀ _
    have h1 := Nat.le_ceil ρ
    have h2 := Nat.le_ceil |e₀.re|
    have h3 := neg_le_abs e₀.re
    linarith
  have hsup : ∀ e₀ ∈ R, ((⌈|e₀.re|⌉₊ : ℕ) : ℝ) ≤ ((R.sup (fun e₀ => ⌈|e₀.re|⌉₊) : ℕ) : ℝ) := by
    intro e₀ he
    exact_mod_cast Finset.le_sup (f := fun e₀ => ⌈|e₀.re|⌉₊) he
  have hBcast : (B : ℝ) = (⌈ρ⌉₊ : ℝ) + ((R.sup (fun e₀ => ⌈|e₀.re|⌉₊) : ℕ) : ℝ) := by
    rw [hB]; push_cast; ring
  have hBle : ∀ e₀ ∈ R, ∀ m : ℕ, (e₀ + (m : ℂ)).re ≤ ρ → m ≤ B := by
    intro e₀ he m hm
    rw [hre_add] at hm
    have h1 := hceil e₀ he
    have h2 := hsup e₀ he
    have : (m : ℝ) ≤ (B : ℝ) := by rw [hBcast]; linarith
    exact_mod_cast this

  set T : Finset ℂ :=
    ((R ×ˢ Finset.range (B + 1)).image (fun p : ℂ × ℕ => p.1 + (p.2 : ℂ))).filter (fun μ => μ.re ≤ ρ) with hT

  set G : Finset ℝ :=
    insert (1 : ℝ)
      (((R ×ˢ Finset.range (B + 2)).image (fun p : ℂ × ℕ => (p.1 + (p.2 : ℂ)).re - ρ)).filter (fun t => 0 < t))
    with hG
  have hGne : G.Nonempty := ⟨1, by rw [hG]; exact Finset.mem_insert_self _ _⟩
  have hGpos : ∀ t ∈ G, 0 < t := by
    intro t ht
    rw [hG, Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · norm_num
    · exact (Finset.mem_filter.1 ht).2
  set δ : ℝ := G.min' hGne / 2 with hδ
  have hδpos : 0 < δ := by
    have := hGpos _ (Finset.min'_mem G hGne)
    rw [hδ]; linarith
  have hmin_le_one : G.min' hGne ≤ 1 := Finset.min'_le _ _ (by rw [hG]; exact Finset.mem_insert_self _ _)

  have hgap : ∀ e₀ ∈ R, ∀ m : ℕ, ρ < (e₀ + (m : ℂ)).re → ρ + 2 * δ ≤ (e₀ + (m : ℂ)).re := by
    intro e₀ he m hm
    by_cases hmB : m ≤ B + 1
    · have hmem : (e₀ + (m : ℂ)).re - ρ ∈ G := by
        rw [hG]
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_filter]
        refine ⟨?_, by linarith⟩
        rw [Finset.mem_image]
        exact ⟨(e₀, m), Finset.mem_product.2 ⟨he, Finset.mem_range.2 (by omega)⟩, rfl⟩
      have h1 : G.min' hGne ≤ (e₀ + (m : ℂ)).re - ρ := Finset.min'_le _ _ hmem
      rw [hδ]; linarith
    · have h2' : B + 2 ≤ m := by omega
      have h2 : (B : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast h2'
      have h3 := hceil e₀ he
      have h4 := hsup e₀ he
      rw [hδ, hre_add]
      rw [hBcast] at h2
      linarith

  have hRmem : ∀ e₀ ∈ R, q.IsRoot e₀ ∨ q'.IsRoot e₀ := by
    intro e₀ he
    rw [hR, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_toFinset, Polynomial.mem_roots hq,
      Polynomial.mem_roots hq'] at he
    exact he
  refine ⟨Fintype.card T, fun i => ((Fintype.equivFin T).symm i : ℂ), δ, hδpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (Fintype.equivFin T).symm.injective (Subtype.ext hij)
  · intro i
    exact (Finset.mem_filter.1 ((Fintype.equivFin T).symm i).2).2
  · intro μ hμ hre
    have hμT : μ ∈ T := by
      refine Finset.mem_filter.2 ⟨?_, hre⟩
      rw [Finset.mem_image]
      rcases hμ with ⟨e₀, he₀, m, rfl⟩ | ⟨e₀, he₀, m, rfl⟩
      · have heR := hmemR e₀ (Or.inl he₀)
        exact ⟨(e₀, m), Finset.mem_product.2 ⟨heR, Finset.mem_range.2 (Nat.lt_succ_of_le (hBle e₀ heR m hre))⟩,
          rfl⟩
      · have heR := hmemR e₀ (Or.inr he₀)
        exact ⟨(e₀, m), Finset.mem_product.2 ⟨heR, Finset.mem_range.2 (Nat.lt_succ_of_le (hBle e₀ heR m hre))⟩,
          rfl⟩
    exact ⟨Fintype.equivFin T ⟨μ, hμT⟩, by simp⟩
  · intro e₀ he₀ m hm
    exact hgap e₀ (hmemR e₀ (Or.inl he₀)) m hm
  · intro e₀ he₀ m hm
    exact hgap e₀ (hmemR e₀ (Or.inr he₀)) m hm
  · intro i
    have hi := (Finset.mem_filter.1 ((Fintype.equivFin T).symm i).2).1
    rw [Finset.mem_image] at hi
    obtain ⟨⟨e₀, m⟩, hp, hμ⟩ := hi
    exact ⟨e₀, hRmem e₀ (Finset.mem_product.1 hp).1, m, hμ.symm⟩

def ExpansionShape (q : Polynomial ℂ) (D : ℕ) : Prop :=
  ∀ (r' d' : ℕ) (L m ρ θ : ℝ),
    (∀ e : ℂ, q.IsRoot e → ∀ n : ℕ, ρ < (e + n).re → θ < (e + n).re) →
    ∃ (S : Finset ℂ) (κ : ℝ),
      (∀ μ ∈ S, μ.re ≤ ρ ∧ ∃ (e : ℂ) (n : ℕ), q.IsRoot e ∧ μ = e + n) ∧
      ∀ (P : Type) [TopologicalSpace P] (M : P → Matrix (Fin r') (Fin r') ℂ)
        (A : P → Fin d' → ((Fin r' → ℂ) →L[ℂ] (Fin r' → ℂ))),
        Continuous M → (∀ p i j, ‖M p i j‖ ≤ L) → (∀ p, Polynomial.aeval (M p) q = 0) →
        (∀ k, Continuous fun p => A p k) → (∀ p k, ‖A p k‖ ≤ L) →
        ∀ (F F' : P → ℝ → (Fin r' → ℂ)) (B : P → ℝ),
        ContinuousOn (fun w : P × ℝ => F w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 1) →
        (∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, B p ≤ B₀) →
        (∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (F p) (F' p y) y ∧
          (y : ℂ) • F' p y =
            (fun i => ∑ j, M p i j • F p y j) + ∑ k : Fin d', ((y : ℂ) ^ ((k : ℕ) + 1)) • A p k (F p y)) →
        (∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F p y‖ ≤ B p * y ^ (-m)) →
        ∃ c : ℂ → ℕ → P → (Fin r' → ℂ),
          (∀ μ j, Continuous (c μ j)) ∧
          ∀ p, (∀ μ j, ‖c μ j p‖ ≤ κ * B p) ∧ (∀ μ ∈ S, μ.re < -m → ∀ j, c μ j p = 0) ∧
            ∀ y ∈ Set.Ioc (0 : ℝ) 1,
              ‖F p y - ∑ μ ∈ S, ∑ j ∈ Finset.range D,
                  ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • c μ j p‖ ≤ κ * B p * y ^ θ

theorem expansion_on_piece {G : Type} [TopologicalSpace G]
    (r d d₂ : ℕ) (q : Polynomial ℂ) (D : ℕ) (hengine : ExpansionShape q D)
    (Mc : G → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (A : G → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
    (hMc : ∀ b, Continuous fun g => Mc g b) (hA : ∀ k b, Continuous fun g => A g k b)
    (K₀ : Set G) (hK₀ : IsCompact K₀) (b : ℝ) (hb : 1 ≤ b)
    (hq0 : ∀ g ∈ K₀, ∀ z : ℝ, 0 < z →
      Polynomial.aeval (∑ b' : Fin (d₂ + 1), ((z : ℂ) ^ (b' : ℕ)) • Mc g b') q = 0)
    (F Fy : ℝ → ℝ → G → (Fin (r + 1) → ℂ))
    (hFcont : ContinuousOn (fun w : ℝ × ℝ × G => F w.1 w.2.1 w.2.2) (Set.Ioc 0 1 ×ˢ Set.Icc b⁻¹ b ×ˢ K₀))
    (hsys : ∀ g ∈ K₀, ∀ z ∈ Set.Icc b⁻¹ b, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F y z g) (Fy y z g) y ∧
      (y : ℂ) • Fy y z g =
        (fun i => ∑ j, (∑ b' : Fin (d₂ + 1), (z : ℂ) ^ (b' : ℕ) * Mc g b' i j) • F y z g j) +
          ∑ k : Fin d, ∑ b' : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b' : ℕ)) • A g k b' (F y z g))
    (m CB : ℝ)
    (hbound : ∀ g ∈ K₀, ∀ z ∈ Set.Icc b⁻¹ b, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y z g‖ ≤ CB * y ^ (-m))
    (ρ θ : ℝ) (hθ : ∀ e : ℂ, q.IsRoot e → ∀ n : ℕ, ρ < (e + n).re → θ < (e + n).re) :
    ∃ (S : Finset ℂ) (κ : ℝ), (∀ μ ∈ S, μ.re ≤ ρ ∧ ∃ (e : ℂ) (n : ℕ), q.IsRoot e ∧ μ = e + n) ∧
      ∃ c : ℂ → ℕ → ℝ → G → (Fin (r + 1) → ℂ),
        (∀ μ j, ContinuousOn (fun w : ℝ × G => c μ j w.1 w.2) (Set.Icc b⁻¹ b ×ˢ K₀)) ∧
        ∀ g ∈ K₀, ∀ z ∈ Set.Icc b⁻¹ b, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖F y z g - ∑ μ ∈ S, ∑ j ∈ Finset.range D,
              ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • c μ j z g‖ ≤ κ * CB * y ^ θ := by
  classical

  set Pset : Set (ℝ × G) := Set.Icc b⁻¹ b ×ˢ K₀ with hPset
  have hPc : IsCompact Pset := isCompact_Icc.prod hK₀
  have hbpos : 0 < b⁻¹ := inv_pos.2 (lt_of_lt_of_le one_pos hb)
  haveI hPcs : CompactSpace Pset := isCompact_iff_compactSpace.1 hPc

  let M : Pset → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
    fun p => ∑ b' : Fin (d₂ + 1), ((p.1.1 : ℂ) ^ (b' : ℕ)) • Mc p.1.2 b'
  let A' : Pset → Fin d → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)) :=
    fun p k => ∑ b' : Fin (d₂ + 1), ((p.1.1 : ℂ) ^ (b' : ℕ)) • A p.1.2 k b'
  have hz_cont : Continuous fun p : Pset => ((p.1.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_fst.comp continuous_subtype_val)
  have hg_cont : Continuous fun p : Pset => p.1.2 := continuous_snd.comp continuous_subtype_val
  have hM_cont : Continuous M := by
    refine continuous_finsetSum _ fun b' _ => ?_
    exact (hz_cont.pow _).smul ((hMc b').comp hg_cont)
  have hA'_cont : ∀ k, Continuous fun p => A' p k := by
    intro k
    refine continuous_finsetSum _ fun b' _ => ?_
    exact (hz_cont.pow _).smul ((hA k b').comp hg_cont)

  have hf_cont : Continuous fun p : Pset =>
      (∑ ij : Fin (r + 1) × Fin (r + 1), ‖M p ij.1 ij.2‖) + ∑ k : Fin d, ‖A' p k‖ := by
    refine Continuous.add ?_ ?_
    · exact continuous_finsetSum _ fun ij _ =>
        ((continuous_apply ij.2).comp ((continuous_apply ij.1).comp hM_cont)).norm
    · exact continuous_finsetSum _ fun k _ => (hA'_cont k).norm
  obtain ⟨L, hL⟩ := isCompact_univ.exists_bound_of_continuousOn hf_cont.continuousOn
  have hL' : ∀ p : Pset,
      (∑ ij : Fin (r + 1) × Fin (r + 1), ‖M p ij.1 ij.2‖) + ∑ k : Fin d, ‖A' p k‖ ≤ L := by
    intro p
    have h := hL p (Set.mem_univ p)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hMbound : ∀ p i j, ‖M p i j‖ ≤ L := by
    intro p i j
    have h2 : ‖M p i j‖ ≤ ∑ ij : Fin (r + 1) × Fin (r + 1), ‖M p ij.1 ij.2‖ :=
      Finset.single_le_sum (f := fun ij : Fin (r + 1) × Fin (r + 1) => ‖M p ij.1 ij.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
    have h3 : 0 ≤ ∑ k : Fin d, ‖A' p k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [hL' p]
  have hA'bound : ∀ p k, ‖A' p k‖ ≤ L := by
    intro p k
    have h2 : ‖A' p k‖ ≤ ∑ k : Fin d, ‖A' p k‖ :=
      Finset.single_le_sum (f := fun k : Fin d => ‖A' p k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have h3 : 0 ≤ ∑ ij : Fin (r + 1) × Fin (r + 1), ‖M p ij.1 ij.2‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [hL' p]
  have hMq : ∀ p : Pset, Polynomial.aeval (M p) q = 0 := by
    intro p
    exact hq0 p.1.2 (Set.mem_prod.1 p.2).2 p.1.1 (lt_of_lt_of_le hbpos (Set.mem_prod.1 p.2).1.1)

  have hφ : Continuous fun w : Pset × ℝ => (w.2, w.1.1.1, w.1.1.2) := by fun_prop
  have hFcont' : ContinuousOn (fun w : Pset × ℝ => F w.2 w.1.1.1 w.1.1.2) (Set.univ ×ˢ Set.Ioc 0 1) := by
    refine hFcont.comp hφ.continuousOn ?_
    intro w hw
    exact Set.mem_prod.2 ⟨(Set.mem_prod.1 hw).2,
      Set.mem_prod.2 ⟨(Set.mem_prod.1 w.1.2).1, (Set.mem_prod.1 w.1.2).2⟩⟩
  have hBloc : ∀ p₀ : Pset, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, (fun _ : Pset => CB) p ≤ B₀ :=
    fun _ => ⟨CB, Filter.Eventually.of_forall fun _ => le_rfl⟩
  have hsys' : ∀ p : Pset, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F y p.1.1 p.1.2) (Fy y p.1.1 p.1.2) y ∧
      (y : ℂ) • Fy y p.1.1 p.1.2 = (fun i => ∑ j, M p i j • F y p.1.1 p.1.2 j) +
        ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A' p k (F y p.1.1 p.1.2) := by
    intro p y hy
    obtain ⟨h1, h2⟩ := hsys p.1.2 (Set.mem_prod.1 p.2).2 p.1.1 (Set.mem_prod.1 p.2).1 y hy
    refine ⟨h1, ?_⟩
    rw [h2]
    congr 1
    · funext i
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp [M, Matrix.sum_apply, Matrix.smul_apply]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [A', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
  have hbound' : ∀ p : Pset, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y p.1.1 p.1.2‖ ≤ (fun _ : Pset => CB) p * y ^ (-m) :=
    fun p y hy => hbound p.1.2 (Set.mem_prod.1 p.2).2 p.1.1 (Set.mem_prod.1 p.2).1 y hy

  obtain ⟨S, κ, hS, hP⟩ := hengine (r + 1) d L m ρ θ hθ
  obtain ⟨c, hc_cont, hc⟩ := hP Pset M A' hM_cont hMbound hMq hA'_cont hA'bound
    (fun p y => F y p.1.1 p.1.2) (fun p y => Fy y p.1.1 p.1.2) (fun _ => CB) hFcont' hBloc hsys' hbound'

  refine ⟨S, κ, hS, fun μ j z g => if h : ((z, g) : ℝ × G) ∈ Pset then c μ j ⟨(z, g), h⟩ else 0, ?_, ?_⟩
  · intro μ j
    rw [continuousOn_iff_continuous_restrict]
    have hrestr : Pset.domRestrict (fun w : ℝ × G =>
        if h : ((w.1, w.2) : ℝ × G) ∈ Pset then c μ j ⟨(w.1, w.2), h⟩ else 0) = c μ j := by
      funext p
      simp [Set.domRestrict_apply, p.2]
    beta_reduce
    rw [hrestr]
    exact hc_cont μ j
  · intro g hg z hz y hy
    have hmem : ((z, g) : ℝ × G) ∈ Pset := Set.mem_prod.2 ⟨hz, hg⟩
    have key := (hc ⟨(z, g), hmem⟩).2.2 y hy
    simp only [dif_pos hmem]
    exact key

theorem sum_reindex_family {n J D : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (S : Finset ℂ)
    (hcov : ∀ μ ∈ S, ∃ i, e i = μ) (hD : D ≤ J) (v : ℂ → ℕ → ℂ) (y : ℝ) :
    ∑ μ ∈ S, ∑ j ∈ Finset.range D, ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) * v μ j =
      ∑ i : Fin n, ∑ j : Fin J,
        (if e i ∈ S ∧ (j : ℕ) < D then v (e i) j else 0) * ((y : ℂ) ^ (e i) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) := by
  classical

  have hinner : ∀ μ : ℂ, ∑ j ∈ Finset.range D, ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) * v μ j =
      ∑ j : Fin J, (if (j : ℕ) < D then v μ j else 0) * (y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ) := by
    intro μ
    rw [Fin.sum_univ_eq_sum_range (fun j => (if j < D then v μ j else 0) * (y : ℂ) ^ μ *
      ((Real.log y : ℝ) : ℂ) ^ j) J]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range J) (fun j => j < D)]
    have h1 : (Finset.range J).filter (fun j => j < D) = Finset.range D := by
      ext j; simp [Finset.mem_filter, Finset.mem_range]; omega
    have h2 : ∑ j ∈ (Finset.range J).filter (fun j => ¬ j < D),
        (if j < D then v μ j else 0) * (y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      simp [hj.2]
    rw [h1, h2, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp [hj]; ring

  have houter : ∑ μ ∈ S, ∑ j : Fin J, (if (j : ℕ) < D then v μ j else 0) * (y : ℂ) ^ μ *
      ((Real.log y : ℝ) : ℂ) ^ (j : ℕ) =
      ∑ i : Fin n, ∑ j : Fin J,
        (if e i ∈ S ∧ (j : ℕ) < D then v (e i) j else 0) * ((y : ℂ) ^ (e i) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) := by
    have himg : S = (Finset.univ.filter (fun i : Fin n => e i ∈ S)).image e := by
      ext μ
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hμ
        obtain ⟨i, hi⟩ := hcov μ hμ
        exact ⟨i, hi ▸ hμ, hi⟩
      · rintro ⟨i, hi, rfl⟩
        exact hi
    have hL : ∑ μ ∈ S, ∑ j : Fin J, (if (j : ℕ) < D then v μ j else 0) * (y : ℂ) ^ μ *
        ((Real.log y : ℝ) : ℂ) ^ (j : ℕ) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => e i ∈ S), ∑ j : Fin J,
          (if (j : ℕ) < D then v (e i) j else 0) * (y : ℂ) ^ (e i) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ) := by
      conv_lhs => rw [himg]
      exact Finset.sum_image (fun i _ j _ hij => he hij)
    rw [hL, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => e i ∈ S)]
    have h0 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ e i ∈ S), ∑ j : Fin J,
        (if e i ∈ S ∧ (j : ℕ) < D then v (e i) j else 0) * ((y : ℂ) ^ (e i) *
          ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_filter] at hi
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hi.2]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hi.2, mul_assoc]
  rw [Finset.sum_congr rfl fun μ _ => hinner μ, houter]

theorem bound_on_piece (C : ℝ) (N : ℕ) (b : ℝ) (hb : 1 ≤ b) (y z : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc b⁻¹ b) :
    C * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N ≤ |C| * b ^ (2 * N) * y ^ (-(N : ℝ)) := by
  have hy0 : 0 < y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have hz0 : 0 < z := lt_of_lt_of_le (inv_pos.2 hb0) hz.1
  have h1 : max y 1 = 1 := max_eq_right hy1
  have h2 : max z 1 ≤ b := max_le hz.2 hb
  have h3 : max y⁻¹ 1 = y⁻¹ := max_eq_left (one_le_inv₀ hy0 |>.2 hy1)
  have h4 : max z⁻¹ 1 ≤ b := by
    refine max_le ?_ hb
    have : z⁻¹ ≤ (b⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hb0) hz.1
    simpa using this
  have hprod : max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1 ≤ b * b * y⁻¹ := by
    rw [h1, h3]
    have hyinv : 0 < y⁻¹ := inv_pos.2 hy0
    calc 1 * max z 1 * y⁻¹ * max z⁻¹ 1 ≤ 1 * b * y⁻¹ * b := by gcongr
      _ = b * b * y⁻¹ := by ring
  have hpow : (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N ≤ (b * b * y⁻¹) ^ N := by
    refine pow_le_pow_left₀ ?_ hprod N
    positivity
  have hrpow : y ^ (-(N : ℝ)) = (y⁻¹) ^ N := by
    rw [Real.rpow_neg hy0.le, Real.rpow_natCast, inv_pow]
  calc C * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N
      ≤ |C| * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N := by
        refine mul_le_mul_of_nonneg_right (le_abs_self C) ?_
        positivity
    _ ≤ |C| * (b * b * y⁻¹) ^ N := by gcongr
    _ = |C| * b ^ (2 * N) * y ^ (-(N : ℝ)) := by
        rw [hrpow, mul_pow, mul_pow, pow_mul, sq]; ring

section ContinuityLemmas

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal Pointwise

theorem continuous_upperUnipotent3_of_entries :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (!![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem ae_mem_adelicBox_of_productionPins :
    ∀ᵐ z ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν,
      z ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  exact ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)

theorem isProbabilityMeasure_ν_of_productionPins_adelicBox :
    @IsProbabilityMeasure _ (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)
    (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne' (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

theorem integrable_adelicBox_of_continuousOn {G : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hG : ContinuousOn G (AdelicBox.adelicBox ℚ)) {M : ℝ} (hM : ∀ z ∈ AdelicBox.adelicBox ℚ, ‖G z‖ ≤ M) :
    Integrable G (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  refine Integrable.mono' (integrable_const M) ?_ (ae_mem_adelicBox_of_productionPins.mono fun z hz => hM z hz)
  rw [productionPinsOf_ν]
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  exact (hG.aestronglyMeasurable (μ := AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    (AdelicBox.measurableSet_adelicBox ℚ)).smul_measure
      (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ))⁻¹

theorem integrable_of_continuous_productionPins {G : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hG : Continuous G) :
    Integrable G (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  obtain ⟨L, hL, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn hG.continuousOn
  exact integrable_adelicBox_of_continuousOn hG.continuousOn fun z hz => hM z (hsub hz)

theorem continuous_integral_of_continuous_productionPins {P : Type} [TopologicalSpace P]
    {F : P → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hF : Continuous fun q : P × AdeleRing (𝓞 ℚ) ℚ => F q.1 q.2) :
    Continuous fun p => ∫ z, F p z ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  obtain ⟨L, hL, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hint : ∀ p, Integrable (F p) (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
    intro p
    have hp : Continuous fun z => F p z := hF.comp (f := fun z => (p, z)) (by fun_prop)
    exact integrable_of_continuous_productionPins hp
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  have hU : TendstoUniformlyOn (fun p z => F p z) (F p₀) (nhds p₀) L :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
      ((ContinuousMap.curry ⟨fun q : P × AdeleRing (𝓞 ℚ) ℚ => F q.1 q.2, hF⟩).continuous.tendsto p₀) L hL
  unfold ContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hU (ε / 2) (half_pos hε)] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le_const (C := ε / 2) ?_) ?_
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with z hz
    rw [← dist_eq_norm, dist_comm]
    exact (hp z (hsub hz)).le
  · rw [probReal_univ, mul_one]
    exact half_lt_self hε

noncomputable def archOfRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : NumberField.InfinitePlace ℚ =>
    ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.IsTotallyReal.isReal v)).symm : ℝ →+* v.Completion)

theorem archRealMat3_eq_mapMatrix (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ (archOfRealHom.mapMatrix (Matrix.of e)) := by
  unfold WhittakerBlock.archRealMat3
  congr 1

theorem archRealMat3_of_mul (e d : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealMat3 e * WhittakerBlock.archRealMat3 d := by
  rw [archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix,
    ← AutomorphicForm.archMatrixInclN_mul, ← map_mul archOfRealHom.mapMatrix]
  rfl

theorem isUnit_archRealMat3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq_mapMatrix]
  have h1 : IsUnit (Matrix.of e) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 he)
  exact (h1.map archOfRealHom.mapMatrix).map (AutomorphicForm.archMatrixInclHomN (Fin 3) ℚ)

theorem coe_archRealLift3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_of_det_ne_zero he)]
  exact IsUnit.unit_spec _

theorem archRealLift3_of_mul {e d : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0)
    (hd : (Matrix.of d).det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 d := by
  have hed : (Matrix.of (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    show (Matrix.of e * Matrix.of d).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero he hd
  apply Units.ext
  rw [Units.val_mul, coe_archRealLift3_of_det_ne_zero he, coe_archRealLift3_of_det_ne_zero hd,
    coe_archRealLift3_of_det_ne_zero hed, archRealMat3_of_mul]

theorem archRealLift3_one_array : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  apply Units.ext
  rw [coe_archRealLift3_of_det_ne_zero (by show (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0; simp),
    archRealMat3_eq_mapMatrix, Units.val_one]
  have h1 : archOfRealHom.mapMatrix (Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
    rw [show Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ) from rfl, map_one]
  rw [h1, AutomorphicForm.archMatrixInclN_one]

theorem isOpen_detSet : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_compl_singleton.preimage h

theorem exists_closedBall_subset_detSet {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall e r ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isOpen_detSet e he
  exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩

theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

theorem contDiff_adjugate_of (k l : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).adjugate k l := by
  fin_cases k <;> fin_cases l <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    fun_prop

theorem contDiffOn_inv_entry (k l : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e)⁻¹ k l)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : ∀ e : Fin 3 → Fin 3 → ℝ, (Matrix.of e)⁻¹ k l = ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate k l := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  simp only [h]
  exact (contDiff_det_of.contDiffOn.inv fun e he => he).mul (contDiff_adjugate_of k l).contDiffOn

theorem continuous_archRealMat3 : Continuous WhittakerBlock.archRealMat3 := by
  refine continuous_matrix fun i j => ?_
  unfold WhittakerBlock.archRealMat3
  simp only [AutomorphicForm.archMatrixInclN, Matrix.of_apply]
  exact (AutomorphicForm.StandardKernel.continuous_ofReal.comp
    ((continuous_apply j).comp (continuous_apply i))).prodMk continuous_const

theorem det_of_inv_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
  show ((Matrix.of e)⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

theorem archRealLift3_inv_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e)⁻¹ =
      WhittakerBlock.archRealLift3 ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h1 : (Matrix.of e * Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    show Matrix.of e * (Matrix.of e)⁻¹ = 1
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← archRealLift3_of_mul he (det_of_inv_ne_zero he), h1, archRealLift3_one_array]

theorem continuousOn_archRealLift3_detSet :
    ContinuousOn WhittakerBlock.archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        ((WhittakerBlock.archRealLift3 e.1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 e.1 :=
      fun e => coe_archRealLift3_of_det_ne_zero e.2
    simp only [Set.restrict, Set.domRestrict_apply, Function.comp_def, h]
    exact continuous_archRealMat3.comp continuous_subtype_val
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        (((WhittakerBlock.archRealLift3 e.1)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 ((Matrix.of e.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
      intro e
      rw [archRealLift3_inv_of_det_ne_zero e.2]
      exact coe_archRealLift3_of_det_ne_zero (det_of_inv_ne_zero e.2)
    simp only [Set.restrict, Set.domRestrict_apply, h]
    refine continuous_archRealMat3.comp ?_
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (contDiffOn_inv_entry k l).continuousOn.comp_continuous continuous_subtype_val fun e => e.2

theorem continuous_whittaker3_of_continuous {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : Continuous u) :
    Continuous (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ u) := by
  have hn : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 q.1.1.2 q.1.2 q.2 :=
    continuous_upperUnipotent3_of_entries.comp
      (by fun_prop : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) ×
          AdeleRing (𝓞 ℚ) ℚ => (q.1.1.2, q.1.2, q.2))
  have hm : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 q.1.1.2 q.1.2 q.2 * q.1.1.1 :=
    hn.mul (by fun_prop)
  have hu' : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      u (upperUnipotent3 q.1.1.2 q.1.2 q.2 * q.1.1.1) :=
    hu.comp hm
  have hp : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      NumberField.StandardAddChar.psiQ (-(q.1.1.2 + q.1.2)) :=
    NumberField.StandardAddChar.continuous_psiQ.comp
      (by fun_prop : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) ×
          AdeleRing (𝓞 ℚ) ℚ => -(q.1.1.2 + q.1.2))
  have hF : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      u (upperUnipotent3 q.1.1.2 q.1.2 q.2 * q.1.1.1) * NumberField.StandardAddChar.psiQ (-(q.1.1.2 + q.1.2)) :=
    hu'.mul hp
  have hA := continuous_integral_of_continuous_productionPins
    (P := (AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ)
    (F := fun q z => u (upperUnipotent3 q.1.2 q.2 z * q.1.1) * NumberField.StandardAddChar.psiQ (-(q.1.2 + q.2))) hF
  have hB := continuous_integral_of_continuous_productionPins (P := AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)
    (F := fun q y => ∫ z, u (upperUnipotent3 q.2 y z * q.1) * NumberField.StandardAddChar.psiQ (-(q.2 + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) hA
  exact continuous_integral_of_continuous_productionPins (P := AdelicGL 3 (𝓞 ℚ) ℚ)
    (F := fun g x => ∫ y, ∫ z, u (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν ∂(productionPinsOf ℚ ∅
            (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) hB

end

end ContinuityLemmas

theorem continuousOn_whittaker3_diag_mul {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f)
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ f
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0) * w.2.2 * k))
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) := by
  have harr : Continuous fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      (fun i j : Fin 3 => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h : i = j
    · subst h
      fin_cases i <;> simp <;> fun_prop
    · simp [h]
      exact continuous_const
  have hdet : ∀ w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ, w ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.univ →
      (Matrix.of (fun i j : Fin 3 => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0)).det ≠ 0 := by
    intro w hw
    have h1 : (0 : ℝ) < w.1 := (Set.mem_prod.1 hw).1
    have h2 : (0 : ℝ) < w.2.1 := (Set.mem_prod.1 (Set.mem_prod.1 hw).2).1
    have hdiag : Matrix.of (fun i j : Fin 3 => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0) =
        Matrix.diagonal ![w.1 * w.2.1, w.2.1, 1] := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [hdiag, Matrix.det_diagonal]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    have h12 : w.1 * w.2.1 * w.2.1 * 1 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero h1.ne' h2.ne') h2.ne') one_ne_zero
    simpa using h12
  have hlift : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      WhittakerBlock.archRealLift3 (fun i j => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0))
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) :=
    continuousOn_archRealLift3_detSet.comp harr.continuousOn fun w hw => hdet w hw
  have hmul : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      WhittakerBlock.archRealLift3 (fun i j => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0) * w.2.2 * k)
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) :=
    (hlift.mul (continuous_snd.comp continuous_snd).continuousOn).mul continuousOn_const
  exact (continuous_whittaker3_of_continuous hf).comp_continuousOn hmul

end A7Port

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.CubicInduction
open scoped Topology
open Filter

namespace JointSliceLib
open A7Port

theorem expansion_on_slab {G : Type} [TopologicalSpace G]
    (r d d₂ : ℕ) (q : Polynomial ℂ) (D : ℕ) (hengine : ExpansionShape q D)
    (Mc : G → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (A : G → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
    (hMc : ∀ b, Continuous fun g => Mc g b) (hA : ∀ k b, Continuous fun g => A g k b)
    (K₀ : Set G) (hK₀ : IsCompact K₀) (Z : ℝ) (hZ : 1 ≤ Z)
    (hq0 : ∀ g ∈ K₀, ∀ z : ℝ, 0 < z →
      Polynomial.aeval (∑ b' : Fin (d₂ + 1), ((z : ℂ) ^ (b' : ℕ)) • Mc g b') q = 0)
    (F Fy : ℝ → ℝ → G → (Fin (r + 1) → ℂ))
    (hFcont : ContinuousOn (fun w : ℝ × ℝ × G => F w.1 w.2.1 w.2.2) (Set.Ioc 0 1 ×ˢ Set.Ioc 0 Z ×ˢ K₀))
    (hsys : ∀ g ∈ K₀, ∀ z ∈ Set.Ioc 0 Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F y z g) (Fy y z g) y ∧
      (y : ℂ) • Fy y z g =
        (fun i => ∑ j, (∑ b' : Fin (d₂ + 1), (z : ℂ) ^ (b' : ℕ) * Mc g b' i j) • F y z g j) +
          ∑ k : Fin d, ∑ b' : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b' : ℕ)) • A g k b' (F y z g))
    (m m' CB : ℝ) (hm' : 0 ≤ m')
    (hbound : ∀ g ∈ K₀, ∀ z ∈ Set.Ioc 0 Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y z g‖ ≤ CB * z ^ (-m') * y ^ (-m))
    (ρ θ : ℝ) (hθ : ∀ e : ℂ, q.IsRoot e → ∀ n : ℕ, ρ < (e + n).re → θ < (e + n).re) :
    ∃ (S : Finset ℂ) (κ : ℝ), (∀ μ ∈ S, μ.re ≤ ρ ∧ ∃ (e : ℂ) (n : ℕ), q.IsRoot e ∧ μ = e + n) ∧
      ∃ c : ℂ → ℕ → ℝ → G → (Fin (r + 1) → ℂ),
        (∀ μ j, ContinuousOn (fun w : ℝ × G => c μ j w.1 w.2) (Set.Ioc 0 Z ×ˢ K₀)) ∧
        ∀ g ∈ K₀, ∀ z ∈ Set.Ioc 0 Z, (∀ μ j, ‖c μ j z g‖ ≤ κ * (CB * z ^ (-m'))) ∧ ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖F y z g - ∑ μ ∈ S, ∑ j ∈ Finset.range D,
              ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • c μ j z g‖ ≤ κ * (CB * z ^ (-m')) * y ^ θ := by
  classical

  set Pset : Set (ℝ × G) := Set.Ioc 0 Z ×ˢ K₀ with hPset

  set Pbig : Set (ℝ × G) := Set.Icc 0 Z ×ˢ K₀ with hPbig
  have hPbigc : IsCompact Pbig := isCompact_Icc.prod hK₀
  have hsub : Pset ⊆ Pbig := Set.prod_mono Set.Ioc_subset_Icc_self le_rfl

  let M : Pset → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
    fun p => ∑ b' : Fin (d₂ + 1), ((p.1.1 : ℂ) ^ (b' : ℕ)) • Mc p.1.2 b'
  let A' : Pset → Fin d → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)) :=
    fun p k => ∑ b' : Fin (d₂ + 1), ((p.1.1 : ℂ) ^ (b' : ℕ)) • A p.1.2 k b'
  have hz_cont : Continuous fun p : Pset => ((p.1.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_fst.comp continuous_subtype_val)
  have hg_cont : Continuous fun p : Pset => p.1.2 := continuous_snd.comp continuous_subtype_val
  have hM_cont : Continuous M := by
    refine continuous_finsetSum _ fun b' _ => ?_
    exact (hz_cont.pow _).smul ((hMc b').comp hg_cont)
  have hA'_cont : ∀ k, Continuous fun p => A' p k := by
    intro k
    refine continuous_finsetSum _ fun b' _ => ?_
    exact (hz_cont.pow _).smul ((hA k b').comp hg_cont)

  let Mbig : ℝ × G → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
    fun w => ∑ b' : Fin (d₂ + 1), ((w.1 : ℂ) ^ (b' : ℕ)) • Mc w.2 b'
  let Abig : ℝ × G → Fin d → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)) :=
    fun w k => ∑ b' : Fin (d₂ + 1), ((w.1 : ℂ) ^ (b' : ℕ)) • A w.2 k b'
  have hMbig_cont : Continuous Mbig := by
    refine continuous_finsetSum _ fun b' _ => ?_
    exact ((Complex.continuous_ofReal.comp continuous_fst).pow _).smul ((hMc b').comp continuous_snd)
  have hAbig_cont : ∀ k, Continuous fun w => Abig w k := by
    intro k
    refine continuous_finsetSum _ fun b' _ => ?_
    exact ((Complex.continuous_ofReal.comp continuous_fst).pow _).smul ((hA k b').comp continuous_snd)
  have hf_cont : Continuous fun w : ℝ × G =>
      (∑ ij : Fin (r + 1) × Fin (r + 1), ‖Mbig w ij.1 ij.2‖) + ∑ k : Fin d, ‖Abig w k‖ := by
    refine Continuous.add ?_ ?_
    · exact continuous_finsetSum _ fun ij _ =>
        ((continuous_apply ij.2).comp ((continuous_apply ij.1).comp hMbig_cont)).norm
    · exact continuous_finsetSum _ fun k _ => (hAbig_cont k).norm
  obtain ⟨L, hL⟩ := hPbigc.exists_bound_of_continuousOn hf_cont.continuousOn
  have hL' : ∀ p : Pset,
      (∑ ij : Fin (r + 1) × Fin (r + 1), ‖M p ij.1 ij.2‖) + ∑ k : Fin d, ‖A' p k‖ ≤ L := by
    intro p
    have h := hL (p : ℝ × G) (hsub p.2)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hMbound : ∀ p i j, ‖M p i j‖ ≤ L := by
    intro p i j
    have h2 : ‖M p i j‖ ≤ ∑ ij : Fin (r + 1) × Fin (r + 1), ‖M p ij.1 ij.2‖ :=
      Finset.single_le_sum (f := fun ij : Fin (r + 1) × Fin (r + 1) => ‖M p ij.1 ij.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
    have h3 : 0 ≤ ∑ k : Fin d, ‖A' p k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [hL' p]
  have hA'bound : ∀ p k, ‖A' p k‖ ≤ L := by
    intro p k
    have h2 : ‖A' p k‖ ≤ ∑ k : Fin d, ‖A' p k‖ :=
      Finset.single_le_sum (f := fun k : Fin d => ‖A' p k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have h3 : 0 ≤ ∑ ij : Fin (r + 1) × Fin (r + 1), ‖M p ij.1 ij.2‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [hL' p]
  have hMq : ∀ p : Pset, Polynomial.aeval (M p) q = 0 := by
    intro p
    exact hq0 p.1.2 (Set.mem_prod.1 p.2).2 p.1.1 (Set.mem_prod.1 p.2).1.1

  have hφ : Continuous fun w : Pset × ℝ => (w.2, w.1.1.1, w.1.1.2) := by fun_prop
  have hFcont' : ContinuousOn (fun w : Pset × ℝ => F w.2 w.1.1.1 w.1.1.2) (Set.univ ×ˢ Set.Ioc 0 1) := by
    refine hFcont.comp hφ.continuousOn ?_
    intro w hw
    exact Set.mem_prod.2 ⟨(Set.mem_prod.1 hw).2,
      Set.mem_prod.2 ⟨(Set.mem_prod.1 w.1.2).1, (Set.mem_prod.1 w.1.2).2⟩⟩
  have hBcont : Continuous fun p : Pset => CB * (p.1.1) ^ (-m') :=
    continuous_const.mul ((continuous_fst.comp continuous_subtype_val).rpow_const
      fun p => Or.inl (ne_of_gt (Set.mem_prod.1 p.2).1.1))
  have hBloc : ∀ p₀ : Pset, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, (fun p : Pset => CB * (p.1.1) ^ (-m')) p ≤ B₀ :=
    fun p₀ => ⟨CB * (p₀.1.1) ^ (-m') + 1,
      (hBcont.continuousAt.eventually_lt (continuous_const.continuousAt) (by linarith)).mono
        fun p hp => hp.le⟩
  have hsys' : ∀ p : Pset, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F y p.1.1 p.1.2) (Fy y p.1.1 p.1.2) y ∧
      (y : ℂ) • Fy y p.1.1 p.1.2 = (fun i => ∑ j, M p i j • F y p.1.1 p.1.2 j) +
        ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A' p k (F y p.1.1 p.1.2) := by
    intro p y hy
    obtain ⟨h1, h2⟩ := hsys p.1.2 (Set.mem_prod.1 p.2).2 p.1.1 (Set.mem_prod.1 p.2).1 y hy
    refine ⟨h1, ?_⟩
    rw [h2]
    congr 1
    · funext i
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp [M, Matrix.sum_apply, Matrix.smul_apply]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [A', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
  have hbound' : ∀ p : Pset, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y p.1.1 p.1.2‖ ≤ (fun p : Pset => CB * (p.1.1) ^ (-m')) p * y ^ (-m) :=
    fun p y hy => hbound p.1.2 (Set.mem_prod.1 p.2).2 p.1.1 (Set.mem_prod.1 p.2).1 y hy

  obtain ⟨S, κ, hS, hP⟩ := hengine (r + 1) d L m ρ θ hθ
  obtain ⟨c, hc_cont, hc⟩ := hP Pset M A' hM_cont hMbound hMq hA'_cont hA'bound
    (fun p y => F y p.1.1 p.1.2) (fun p y => Fy y p.1.1 p.1.2) (fun p : Pset => CB * (p.1.1) ^ (-m')) hFcont' hBloc hsys' hbound'

  refine ⟨S, κ, hS, fun μ j z g => if h : ((z, g) : ℝ × G) ∈ Pset then c μ j ⟨(z, g), h⟩ else 0, ?_, ?_⟩
  · intro μ j
    rw [continuousOn_iff_continuous_restrict]
    have hrestr : Pset.domRestrict (fun w : ℝ × G =>
        if h : ((w.1, w.2) : ℝ × G) ∈ Pset then c μ j ⟨(w.1, w.2), h⟩ else 0) = c μ j := by
      funext p
      simp [Set.domRestrict_apply, p.2]
    beta_reduce
    rw [hrestr]
    exact hc_cont μ j
  · intro g hg z hz
    have hmem : ((z, g) : ℝ × G) ∈ Pset := Set.mem_prod.2 ⟨hz, hg⟩
    refine ⟨fun μ j => ?_, fun y hy => ?_⟩
    · have key := (hc ⟨(z, g), hmem⟩).1 μ j
      simp only [dif_pos hmem]
      exact key
    · have key := (hc ⟨(z, g), hmem⟩).2.2 y hy
      simp only [dif_pos hmem]
      exact key

theorem bound_on_slab (C : ℝ) (N : ℕ) (Z : ℝ) (hZ : 1 ≤ Z) (y z : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1)
    (hz : z ∈ Set.Ioc (0 : ℝ) Z) :
    C * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N ≤ |C| * Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) := by
  have hy0 := hy.1
  have hz0 := hz.1
  have h1 : max y 1 = 1 := max_eq_right hy.2
  have h2 : max z 1 ≤ Z := max_le hz.2 hZ
  have h3 : max y⁻¹ 1 = y⁻¹ := max_eq_left (one_le_inv₀ hy0 |>.2 hy.2)
  have h4 : max z⁻¹ 1 ≤ Z * z⁻¹ := by
    refine max_le ?_ ?_
    · calc z⁻¹ = 1 * z⁻¹ := (one_mul _).symm
        _ ≤ Z * z⁻¹ := mul_le_mul_of_nonneg_right hZ (inv_nonneg.2 hz0.le)
    · rw [← div_eq_mul_inv]; exact (one_le_div hz0).2 hz.2
  have hprod : max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1 ≤ Z ^ 2 * (z⁻¹ * y⁻¹) := by
    rw [h1, h3, one_mul]
    calc max z 1 * y⁻¹ * max z⁻¹ 1 ≤ Z * y⁻¹ * (Z * z⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hy0.le)) h4
            (le_trans zero_le_one (le_max_right _ _))
            (mul_nonneg (by linarith) (inv_nonneg.2 hy0.le))
      _ = Z ^ 2 * (z⁻¹ * y⁻¹) := by ring
  have hnn : 0 ≤ max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1 := by positivity
  have hpow : (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N ≤ Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) := by
    calc (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N ≤ (Z ^ 2 * (z⁻¹ * y⁻¹)) ^ N :=
          pow_le_pow_left₀ hnn hprod N
      _ = Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) := by
          rw [mul_pow, mul_pow, ← pow_mul, Real.rpow_neg hz0.le, Real.rpow_neg hy0.le, Real.rpow_natCast,
            Real.rpow_natCast, inv_pow, inv_pow]
          ring
  have hR : 0 ≤ Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg hz0.le _)) (Real.rpow_nonneg hy0.le _)
  calc C * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N ≤ |C| * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hnn N)
    _ ≤ |C| * (Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ))) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = |C| * Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) := by ring

theorem expansion_on_slice_first_vec_slab
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e) (δ : ℝ) (hδ : 0 < δ)
    (q : Polynomial ℂ)
    (hcov : ∀ μ : ℂ, (∃ e₀ : ℂ, q.IsRoot e₀ ∧ ∃ m : ℕ, μ = e₀ + m) → μ.re ≤ ρ → ∃ i, e i = μ)
    (hgap : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ m : ℕ, ρ < (e₀ + m).re → ρ + 2 * δ ≤ (e₀ + m).re)
    (D : ℕ) (hDJ : D ≤ J) (hengine : ExpansionShape q D)
    (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (h1 : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (h8 : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N)
    (r d d₂ : ℕ) (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (Mc : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (A : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
    (hw0 : w 0 = []) (hκ0 : κ 0 = 1)
    (hMc : ∀ b, Continuous fun g => Mc g b) (hA : ∀ k b, Continuous fun g => A g k b)
    (hq0 : ∀ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
      ∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc g₀ b) q = 0)
    (hsys : ∀ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
      ∀ F : ℝ → ℝ → (Fin (r + 1) → ℂ),
      (∀ (y z : ℝ) (i : Fin (r + 1)), F y z i =
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κ i)) →
      ∃ Fy : ℝ → ℝ → (Fin (r + 1) → ℂ),
      ∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => F y z) (Fy y z) y ∧
        (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g₀ b i j) • F y z j) +
          ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
            ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g₀ k b (F y z))
    (K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK₀ : IsCompact K₀)
    (horth : ∀ k ∈ K₀, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (Z : ℝ) (hZ : 1 ≤ Z) :
    ∃ Cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → (Fin (r + 1) → ℂ),
      (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => Cv i j p.1 p.2) (Set.Ioc 0 Z ×ˢ K₀)) ∧
      ∃ C : ℝ, ∀ k ∈ K₀, ∀ y₂ ∈ Set.Ioc (0 : ℝ) Z,
        (∀ i j, ‖Cv i j y₂ k‖ ≤ C * y₂ ^ (-(N : ℝ))) ∧
        ∀ y₁ ∈ Set.Ioc (0 : ℝ) 1,
        ‖(fun l : Fin (r + 1) => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ
            (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w l))
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k * κ l)) -
          (∑ i : Fin n, ∑ j : Fin J, ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) • Cv i j y₂ k)‖ ≤
        C * y₂ ^ (-(N : ℝ)) * y₁ ^ (ρ + δ) := by
  classical
  have hZ0 : 0 < Z := lt_of_lt_of_le one_pos hZ

  set F : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → (Fin (r + 1) → ℂ) := fun y z g i =>
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ
      (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g * κ i) with hFdef
  have hFy : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g ∈ orth3 →
      ∃ Fy : ℝ → ℝ → (Fin (r + 1) → ℂ), ∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y →
        HasDerivAt (fun y => F y z g) (Fy y z) y ∧
        (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g b i j) • F y z g j) +
          ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g k b (F y z g) :=
    fun g hg => hsys g hg (fun y z => F y z g) (fun y z i => rfl)
  choose! Fy hFy using hFy

  have hS3 : ∀ i : Fin (r + 1), ∃ C : ℝ, ∀ g ∈ K₀, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      ‖F y₁ y₂ g i‖ ≤ C * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N := by
    intro i
    have hcw : ∀ w' : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
        (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i)) w') := by
      intro w'
      have h := h1 (w' ++ w i)
      rwa [List.foldr_append] at h
    have hgr : ∀ w' : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i)) w' g‖ ≤ C * gauge3 ℚ g ^ N := by
      intro w'
      obtain ⟨C, hC⟩ := h8 (w' ++ w i)
      refine ⟨C, fun g => ?_⟩
      have h := hC g
      rwa [List.foldr_append] at h
    obtain ⟨C, hC⟩ := LanglandsTunnell.CubicInduction.norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact N _
      hcw hgr ((fun g => g * κ i) '' K₀) (hK₀.image (continuous_id.mul continuous_const))
    refine ⟨C, fun g hg y₁ y₂ hy₁ hy₂ => ?_⟩
    have h := hC (g * κ i) ⟨g, hg, rfl⟩ y₁ y₂ hy₁ hy₂
    simpa only [F, mul_assoc] using h
  choose CS hCS using hS3
  set CB : ℝ := (∑ i : Fin (r + 1), |CS i|) * Z ^ (2 * N) with hCB
  have hCB0 : 0 ≤ CB := by
    rw [hCB]
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (pow_nonneg hZ0.le _)
  have hbound : ∀ g ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y z g‖ ≤ CB * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) := by
    intro g hg z hz y hy
    have hy0 : 0 < y := hy.1
    have hz0 : 0 < z := hz.1
    have hyN : 0 ≤ y ^ (-(N : ℝ)) := Real.rpow_nonneg hy0.le _
    have hzN : 0 ≤ z ^ (-(N : ℝ)) := Real.rpow_nonneg hz0.le _
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hCB0 hzN) hyN)]
    intro i
    have h1' : |CS i| ≤ ∑ i : Fin (r + 1), |CS i| :=
      Finset.single_le_sum (f := fun i => |CS i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2' : (0 : ℝ) ≤ Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) :=
      mul_nonneg (mul_nonneg (pow_nonneg hZ0.le _) hzN) hyN
    calc ‖F y z g i‖ ≤ CS i * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N := hCS i g hg y z hy0 hz0
      _ ≤ |CS i| * Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) := bound_on_slab (CS i) N Z hZ y z hy hz
      _ = |CS i| * (Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ))) := by ring
      _ ≤ (∑ i : Fin (r + 1), |CS i|) * (Z ^ (2 * N) * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ))) :=
          mul_le_mul_of_nonneg_right h1' h2'
      _ = CB * z ^ (-(N : ℝ)) * y ^ (-(N : ℝ)) := by rw [hCB]; ring

  have hθ : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ m : ℕ, ρ < (e₀ + m).re → ρ + δ < (e₀ + m).re := by
    intro e₀ he₀ m hm
    have h := hgap e₀ he₀ m hm
    linarith

  have hFcont : ContinuousOn (fun p : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => F p.1 p.2.1 p.2.2)
      (Set.Ioc 0 1 ×ˢ Set.Ioc 0 Z ×ˢ K₀) := by
    refine continuousOn_pi.2 fun i => ?_
    refine (continuousOn_whittaker3_diag_mul (h1 (w i)) (κ i)).mono ?_
    intro p hp
    have hp1 : p.1 ∈ Set.Ioc (0 : ℝ) 1 := (Set.mem_prod.1 hp).1
    have hp2 : p.2.1 ∈ Set.Ioc (0 : ℝ) Z := (Set.mem_prod.1 (Set.mem_prod.1 hp).2).1
    exact Set.mem_prod.2 ⟨hp1.1, Set.mem_prod.2 ⟨hp2.1, Set.mem_univ _⟩⟩
  have hsys' : ∀ g ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F y z g) (Fy g y z) y ∧
      (y : ℂ) • Fy g y z =
        (fun i => ∑ j, (∑ b' : Fin (d₂ + 1), (z : ℂ) ^ (b' : ℕ) * Mc g b' i j) • F y z g j) +
          ∑ k : Fin d, ∑ b' : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b' : ℕ)) • A g k b' (F y z g) :=
    fun g hg z hz y hy => hFy g (horth g hg) z hz.1 y hy.1

  obtain ⟨S, κ', hS, c, hc_cont, hc⟩ := expansion_on_slab r d d₂ q D hengine Mc A hMc hA K₀ hK₀ Z hZ
    (fun g hg z hz => hq0 g (horth g hg) z hz) F (fun y z g => Fy g y z) hFcont hsys' (N : ℝ) (N : ℝ) CB
    (Nat.cast_nonneg N) hbound ρ (ρ + δ) hθ
  have hcovS : ∀ μ ∈ S, ∃ i, e i = μ := by
    intro μ hμ
    obtain ⟨hre, e₀, m, hr, hm⟩ := hS μ hμ
    exact hcov μ ⟨e₀, hr, m, hm⟩ hre

  have hκ'0 : 0 ≤ κ' * CB ∨ True := Or.inr trivial
  refine ⟨fun i j z g => if e i ∈ S ∧ (j : ℕ) < D then c (e i) j z g else 0, ?_, ?_⟩
  · intro i j
    by_cases hij : e i ∈ S ∧ (j : ℕ) < D
    · simp only [if_pos hij]
      exact hc_cont (e i) j
    · simp only [if_neg hij]
      exact continuousOn_const
  · refine ⟨max (κ' * CB) 0, fun g hg y₂ hy₂ => ⟨fun i j => ?_, fun y₁ hy₁ => ?_⟩⟩
    · have hzN : 0 ≤ y₂ ^ (-(N : ℝ)) := Real.rpow_nonneg hy₂.1.le _
      by_cases hij : e i ∈ S ∧ (j : ℕ) < D
      · simp only [if_pos hij]
        calc ‖c (e i) j y₂ g‖ ≤ κ' * (CB * y₂ ^ (-(N : ℝ))) := (hc g hg y₂ hy₂).1 (e i) j
          _ = κ' * CB * y₂ ^ (-(N : ℝ)) := by ring
          _ ≤ max (κ' * CB) 0 * y₂ ^ (-(N : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hzN
      · simp only [if_neg hij, norm_zero]
        exact mul_nonneg (le_max_right _ _) hzN
    · have hmain := (hc g hg y₂ hy₂).2 y₁ hy₁
      have hvec : (∑ μ ∈ S, ∑ j ∈ Finset.range D,
          ((y₁ : ℂ) ^ μ * ((Real.log y₁ : ℝ) : ℂ) ^ j) • c μ j y₂ g) =
          ∑ i : Fin n, ∑ j : Fin J, ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) •
            (if e i ∈ S ∧ (j : ℕ) < D then c (e i) j y₂ g else 0) := by
        funext a
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have h := sum_reindex_family e he S hcovS hDJ (fun μ j => c μ j y₂ g a) y₁
        rw [h]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp [mul_comm]
      have hF : F y₁ y₂ g = fun l : Fin (r + 1) =>
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ
            (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w l))
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * g * κ l) := rfl
      rw [← hF, ← hvec]
      refine hmain.trans ?_
      have hpos : 0 ≤ y₂ ^ (-(N : ℝ)) * y₁ ^ (ρ + δ) :=
        mul_nonneg (Real.rpow_nonneg hy₂.1.le _) (Real.rpow_nonneg hy₁.1.le _)
      calc κ' * (CB * y₂ ^ (-(N : ℝ))) * y₁ ^ (ρ + δ) = κ' * CB * (y₂ ^ (-(N : ℝ)) * y₁ ^ (ρ + δ)) := by ring
        _ ≤ max (κ' * CB) 0 * (y₂ ^ (-(N : ℝ)) * y₁ ^ (ρ + δ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
        _ = max (κ' * CB) 0 * y₂ ^ (-(N : ℝ)) * y₁ ^ (ρ + δ) := by ring

theorem second_expansion_on_compact
    {G : Type} [TopologicalSpace G] {n J r d' d₂' : ℕ}
    (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ (i : Fin n) (m : ℕ), (e i + m).re ≤ ρ → ∃ i', e i' = e i + m)
    (hgapF : ∀ (i : Fin n) (m : ℕ), ρ < (e i + m).re → ρ + 2 * δ ≤ (e i + m).re)
    (q' : Polynomial ℂ) (hq' : q' ≠ 0)
    (hgap' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ m : ℕ, ρ < (e₀ + m).re → ρ + 2 * δ ≤ (e₀ + m).re)
    (K₀ : Set G) (hK₀ : IsCompact K₀)
    (Mc' : G → Fin (d₂' + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (A' : G → Fin d' → Fin (d₂' + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
    (hMc' : ∀ a, Continuous fun g => Mc' g a) (hA' : ∀ k a, Continuous fun g => A' g k a)
    (hq0' : ∀ g ∈ K₀, ∀ y : ℝ, 0 < y →
      Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' g a) q' = 0)
    (F Fz : ℝ → ℝ → G → (Fin (r + 1) → ℂ))
    (hsysz : ∀ g ∈ K₀, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 2,
      HasDerivAt (fun z => F y z g) (Fz y z g) z ∧
      (z : ℂ) • Fz y z g = (fun a => ∑ b, (∑ a' : Fin (d₂' + 1), (y : ℂ) ^ (a' : ℕ) * Mc' g a' a b) • F y z g b) +
        ∑ k : Fin d', ∑ a' : Fin (d₂' + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a' : ℕ)) • A' g k a' (F y z g))
    (Cv : Fin n → Fin J → ℝ → G → (Fin (r + 1) → ℂ))
    (hCv_cont : ∀ i j, ContinuousOn (fun p : ℝ × G => Cv i j p.1 p.2) (Set.Ioc 0 2 ×ˢ K₀))
    (CB N : ℝ) (hCB : 0 ≤ CB)
    (hCv_bd : ∀ g ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ i j, ‖Cv i j z g‖ ≤ CB * z ^ (-N))
    (hCv_exp : ∀ g ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y z g - ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • Cv i j z g‖ ≤
        CB * z ^ (-N) * y ^ (ρ + δ)) :
    ∃ (D₂ : ℕ) (S₂ : Finset ℂ) (κ : ℝ), D₂ ≤ n * q'.natDegree ∧
      (∀ μ ∈ S₂, μ.re ≤ ρ ∧ ∃ (e' : ℂ) (N' : ℕ), q'.IsRoot e' ∧ μ = e' + N') ∧
      ∃ c₂ : ℂ → ℕ → ↥K₀ → Fin n → Fin J → (Fin (r + 1) → ℂ),
        (∀ μ j₂ i j, Continuous fun p => c₂ μ j₂ p i j) ∧
        ∀ (p : ↥K₀) i j, (∀ μ j₂, ‖c₂ μ j₂ p i j‖ ≤ κ * CB) ∧
          ∀ z ∈ Set.Ioc (0 : ℝ) 1,
            ‖Cv i j z p.1 - ∑ μ ∈ S₂, ∑ j₂ ∈ Finset.range D₂,
                ((z : ℂ) ^ μ * ((Real.log z : ℝ) : ℂ) ^ j₂) • c₂ μ j₂ p i j‖ ≤ κ * CB * z ^ (ρ + δ) := by
  classical

  have hf_cont : Continuous fun g : G =>
      (∑ a : Fin (d₂' + 1), ∑ ij : Fin (r + 1) × Fin (r + 1), ‖Mc' g a ij.1 ij.2‖) +
        ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ‖A' g k a‖ := by
    refine Continuous.add ?_ ?_
    · exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun ij _ =>
        ((continuous_apply ij.2).comp ((continuous_apply ij.1).comp (hMc' a))).norm
    · exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun a _ => (hA' k a).norm
  obtain ⟨L, hL⟩ := hK₀.exists_bound_of_continuousOn hf_cont.continuousOn
  have hL' : ∀ g ∈ K₀, (∑ a : Fin (d₂' + 1), ∑ ij : Fin (r + 1) × Fin (r + 1), ‖Mc' g a ij.1 ij.2‖) +
      ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ‖A' g k a‖ ≤ L := by
    intro g hg
    have h := hL g hg
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hMcL : ∀ (p : ↥K₀) a i j, ‖Mc' p.1 a i j‖ ≤ L := by
    intro p a i j
    have h1 : ‖Mc' p.1 a i j‖ ≤ ∑ ij : Fin (r + 1) × Fin (r + 1), ‖Mc' p.1 a ij.1 ij.2‖ :=
      Finset.single_le_sum (f := fun ij : Fin (r + 1) × Fin (r + 1) => ‖Mc' p.1 a ij.1 ij.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
    have h2 : ∑ ij : Fin (r + 1) × Fin (r + 1), ‖Mc' p.1 a ij.1 ij.2‖ ≤
        ∑ a : Fin (d₂' + 1), ∑ ij : Fin (r + 1) × Fin (r + 1), ‖Mc' p.1 a ij.1 ij.2‖ :=
      Finset.single_le_sum (f := fun a => ∑ ij : Fin (r + 1) × Fin (r + 1), ‖Mc' p.1 a ij.1 ij.2‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have h3 : 0 ≤ ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [hL' p.1 p.2]
  have hAL : ∀ (p : ↥K₀) k a, ‖A' p.1 k a‖ ≤ L := by
    intro p k a
    have h1 : ‖A' p.1 k a‖ ≤ ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖ :=
      Finset.single_le_sum (f := fun a => ‖A' p.1 k a‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have h2 : ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖ ≤ ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖ :=
      Finset.single_le_sum (f := fun k => ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have h3 : 0 ≤ ∑ a : Fin (d₂' + 1), ∑ ij : Fin (r + 1) × Fin (r + 1), ‖Mc' p.1 a ij.1 ij.2‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [hL' p.1 p.2]

  have hann : ∀ p : ↥K₀, Polynomial.aeval (Mc' p.1 0) q' = 0 := fun p =>
    Polynomial.aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero (r + 1) d₂' (Mc' p.1) q' (hq0' p.1 p.2)

  have hfold : ∀ (p : ↥K₀) (i : Fin n) (j : Fin J), ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun z => Cv i j z p.1)
        ((z : ℂ)⁻¹ • ∑ a : Fin (d₂' + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
          Matrix.mulVec (Mc' p.1 a) (Cv i' j z p.1) +
            ∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' p.1 k a (Cv i' j z p.1)
        else 0) z := by
    intro p i j z hz
    have hC : ∀ i j, ContinuousOn (fun z => Cv i j z p.1) (Set.Ioc 0 2) := by
      intro i j
      have hφ : Continuous fun z : ℝ => ((z, p.1) : ℝ × G) := by fun_prop
      exact (hCv_cont i j).comp hφ.continuousOn fun z hz => Set.mem_prod.2 ⟨hz, p.2⟩
    have hexp : ∀ z₀ ∈ Set.Ioc (0 : ℝ) 2, ∃ K ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioc (0 : ℝ) 2, |z - z₀| < ε →
        ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖F y z p.1 - ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • Cv i j z p.1‖ ≤
            K * y ^ (ρ + δ) := by
      intro z₀ hz₀
      refine ⟨CB * (z₀ / 2) ^ (-N) + CB * (2 : ℝ) ^ (-N) + CB * (z₀ / 2) ^ N * 0 + CB * ((z₀/2) ^ (-N) + (2:ℝ) ^ (-N)) * 0
        + CB * max ((z₀ / 2) ^ (-N)) ((2 : ℝ) ^ (-N)), z₀ / 2, by linarith [hz₀.1], ?_⟩
      intro z hz hzz y hy
      have hz2 : z₀ / 2 ≤ z := by have := (abs_lt.1 hzz).1; linarith
      refine (hCv_exp p.1 p.2 z hz y hy).trans ?_
      have hyp : 0 ≤ y ^ (ρ + δ) := Real.rpow_nonneg hy.1.le _
      refine mul_le_mul_of_nonneg_right ?_ hyp

      have hzN : z ^ (-N) ≤ max ((z₀ / 2) ^ (-N)) ((2 : ℝ) ^ (-N)) := by
        rcases le_or_gt 0 (-N) with hN | hN
        · exact (Real.rpow_le_rpow hz.1.le hz.2 hN).trans (le_max_right _ _)
        · exact (Real.rpow_le_rpow_of_nonpos (by linarith [hz₀.1]) hz2 hN.le).trans (le_max_left _ _)
      have h1 : CB * z ^ (-N) ≤ CB * max ((z₀ / 2) ^ (-N)) ((2 : ℝ) ^ (-N)) := mul_le_mul_of_nonneg_left hzN hCB
      have hnn1 : 0 ≤ CB * (z₀ / 2) ^ (-N) := mul_nonneg hCB (Real.rpow_nonneg (by linarith [hz₀.1]) _)
      have hnn2 : 0 ≤ CB * (2 : ℝ) ^ (-N) := mul_nonneg hCB (Real.rpow_nonneg (by norm_num) _)
      linarith
    exact RegularSingular.hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le e he ρ δ hδ hre hcl
      hgapF (Mc' p.1) (A' p.1) (fun y z => F y z p.1) (fun y z => Fz y z p.1)
      (fun y hy z hz => hsysz p.1 p.2 y hy z hz) (fun i j z => Cv i j z p.1) hC hexp i j z
      ⟨hz.1, lt_of_le_of_lt hz.2 one_lt_two⟩

  have hθ : ∀ e' : ℂ, q'.IsRoot e' → ∀ N' : ℕ, ρ < (e' + N').re → ρ + δ < (e' + N').re := by
    intro e' he' N' hN'
    have h := hgap' e' he' N' hN'
    linarith

  have key := RegularSingular.exists_expansion_coeff_of_folded_system (n := n) (J := J) (R := r + 1)
    (d₂ := d₂') (d := d') e he (↥K₀) (fun p a => Mc' p.1 a) (fun p k a => A' p.1 k a) L
    (fun a => (hMc' a).comp continuous_subtype_val) hMcL
    (fun k a => (hA' k a).comp continuous_subtype_val) hAL q' hq' hann
    (fun p i j z => Cv i j z p.1)
    (fun p i j z => (z : ℂ)⁻¹ • ∑ a : Fin (d₂' + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
        Matrix.mulVec (Mc' p.1 a) (Cv i' j z p.1) +
          ∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' p.1 k a (Cv i' j z p.1)
      else 0)
    ?_ ?_ N (fun _ => CB) (fun _ => ⟨CB, Filter.Eventually.of_forall fun _ => le_rfl⟩) ?_ ρ (ρ + δ) hθ
  · obtain ⟨D₂, S₂, κ, hD₂, hS₂, c₂, hc₂_cont, hc₂⟩ := key
    exact ⟨D₂, S₂, κ, hD₂, hS₂, c₂, hc₂_cont, hc₂⟩
  ·
    intro i j
    have hφ : Continuous fun w : ↥K₀ × ℝ => ((w.2, w.1.1) : ℝ × G) := by fun_prop
    refine (hCv_cont i j).comp hφ.continuousOn ?_
    intro w hw
    exact Set.mem_prod.2 ⟨⟨(Set.mem_prod.1 hw).2.1, ((Set.mem_prod.1 hw).2.2).trans one_le_two⟩, w.1.2⟩
  ·
    intro p i j z hz
    refine ⟨hfold p i j z hz, ?_⟩
    have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz.1.ne'
    rw [smul_inv_smul₀ hzC]
  ·
    intro p i j z hz
    exact hCv_bd p.1 p.2 z ⟨hz.1, hz.2.trans one_le_two⟩ i j

end JointSliceLib

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.CubicInduction
open scoped Topology
open Filter

namespace Fold0Aux

abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ

noncomputable abbrev Wh (φ : G3 → ℂ) : G3 → ℂ :=
  whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
    NumberField.StandardAddChar.psiQ φ

noncomputable abbrev tor (y z : ℝ) : G3 :=
  WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0)

noncomputable abbrev wordFn (u : G3 → ℂ) (w : List (Fin 3 × Fin 3)) : G3 → ℂ :=
  List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w

abbrev IsOrthArch (k : G3) : Prop :=
  (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3

theorem wordFn_nil (u : G3 → ℂ) : wordFn u [] = u := rfl

theorem wordFn_cons (u : G3 → ℂ) (p : Fin 3 × Fin 3) (w : List (Fin 3 × Fin 3)) :
    wordFn u (p :: w) = WhittakerBlock.archDeriv p.1 p.2 (wordFn u w) := rfl

theorem wordFn_append (u : G3 → ℂ) (w w' : List (Fin 3 × Fin 3)) :
    wordFn u (w ++ w') = wordFn (wordFn u w') w := by
  simp only [wordFn, List.foldr_append]

theorem wordFn_archDeriv (u : G3 → ℂ) (i j : Fin 3) (w : List (Fin 3 × Fin 3)) :
    wordFn (WhittakerBlock.archDeriv i j u) w = wordFn u (w ++ [(i, j)]) := by
  rw [wordFn_append]; rfl

structure InBlock (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) {N₂ : ℕ} (a₂ : Fin (N₂ + 1) → ℂ) {N₃ : ℕ}
    (a₃ : Fin (N₃ + 1) → ℂ) (N : ℕ) (u : G3 → ℂ) : Prop where
  h1 : ∀ w : List (Fin 3 × Fin 3), Continuous (wordFn u w)
  h2 : ∀ (γ : GL (Fin 3) ℚ) (g : G3), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g
  h3 : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : G3), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g
  h4 : WhittakerBlock.IsArchSmooth3 u
  h5 : ∃ s : Finset (G3 → ℂ), ∀ k : G3, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) →
    archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 → (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (G3 → ℂ))
  h6 : (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u)) = 0
  h7 : (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u)) = 0
  h8 : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : G3, ‖wordFn u w g‖ ≤ C * gauge3 ℚ g ^ N

theorem archDeriv_mul_left_invariant {u : G3 → ℂ} {x : G3} (hx : ∀ g, u (x * g) = u g) (i j : Fin 3)
    (g : G3) : WhittakerBlock.archDeriv i j u (x * g) = WhittakerBlock.archDeriv i j u g := by
  show deriv _ 0 = deriv _ 0
  congr 1
  funext s
  rw [mul_assoc, hx]

theorem archDeriv_mul_left_char {u : G3 → ℂ} {x : G3} {c : ℂ} (hx : ∀ g, u (x * g) = c * u g) (i j : Fin 3)
    (g : G3) : WhittakerBlock.archDeriv i j u (x * g) = c * WhittakerBlock.archDeriv i j u g := by
  show deriv _ 0 = c * deriv _ 0
  rw [← deriv_const_mul_field c]
  congr 1
  funext s
  rw [mul_assoc, hx]

theorem kfinite_archDeriv {u : G3 → ℂ} (h4 : WhittakerBlock.IsArchSmooth3 u)
    (h5 : ∃ s : Finset (G3 → ℂ), ∀ k : G3, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) →
      archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 → (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (G3 → ℂ)))
    (i j : Fin 3) :
    ∃ s : Finset (G3 → ℂ), ∀ k : G3, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) →
      archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => WhittakerBlock.archDeriv i j u (g * k)) ∈ Submodule.span ℂ (s : Set (G3 → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := h5

  let V : Submodule ℂ (G3 → ℂ) := Submodule.span ℂ {φ | ∃ k : G3, IsOrthArch k ∧ φ = fun g => u (g * k)}
  have hVle : V ≤ Submodule.span ℂ (s : Set (G3 → ℂ)) := by
    refine Submodule.span_le.2 ?_
    rintro φ ⟨k, hk, rfl⟩
    exact hs k hk.1 hk.2
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (s : Set (G3 → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  haveI hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVle
  have hVsm : ∀ φ ∈ V, WhittakerBlock.IsArchSmooth3 φ := by
    have hle : V ≤ WhittakerBlock.smoothFunctions3 := by
      refine Submodule.span_le.2 ?_
      rintro φ ⟨k, -, rfl⟩
      exact isArchSmooth3_mul_right u h4 k
    intro φ hφ
    exact hle hφ
  obtain ⟨-, hadd, hsmul, -, -⟩ := WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate

  let L : Fin 3 × Fin 3 → (V →ₗ[ℂ] (G3 → ℂ)) := fun pq =>
    { toFun := fun φ => WhittakerBlock.archDeriv pq.1 pq.2 (φ : G3 → ℂ)
      map_add' := fun φ ψ => by
        simpa only [Submodule.coe_add] using hadd φ ψ (hVsm φ φ.2) (hVsm ψ ψ.2) pq.1 pq.2
      map_smul' := fun c φ => by
        simpa only [Submodule.coe_smul, RingHom.id_apply] using hsmul c φ pq.1 pq.2 }
  have hfg : ∀ pq, (LinearMap.range (L pq)).FG := fun pq =>
    (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  choose t ht using hfg
  refine ⟨Finset.univ.biUnion t, fun k hk hk' => ?_⟩
  obtain ⟨n, c, ws, hlen, hsum⟩ := foldr_archDeriv_mul_right_eq_sum [(i, j)] k
  have hmem : (fun g => u (g * k)) ∈ V := Submodule.subset_span ⟨k, ⟨hk, hk'⟩, rfl⟩

  have hws : ∀ m, ∃ pq, ws m = [pq] := fun m => List.length_eq_one_iff.1 (by simpa using hlen m)
  choose pq hpq using hws
  have hfun : (fun g => WhittakerBlock.archDeriv i j u (g * k)) =
      ∑ m, c m • L (pq m) ⟨fun g => u (g * k), hmem⟩ := by
    funext g
    have := hsum u h4 g
    simp only [List.foldr_cons, List.foldr_nil] at this
    rw [this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hpq m]
    simp only [Pi.smul_apply, smul_eq_mul, List.foldr_cons, List.foldr_nil]
    rfl
  rw [hfun]
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  have hr : L (pq m) ⟨fun g => u (g * k), hmem⟩ ∈ LinearMap.range (L (pq m)) := LinearMap.mem_range_self _ _
  rw [← ht (pq m)] at hr
  exact Submodule.span_mono (by
    intro x hx
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨pq m, Finset.mem_univ _, Finset.mem_coe.1 hx⟩)) hr

theorem InBlock.archDeriv {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {N₂ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ} {N₃ : ℕ}
    {a₃ : Fin (N₃ + 1) → ℂ} {N : ℕ} {u : G3 → ℂ} (hu : InBlock ω a₂ a₃ N u) (i j : Fin 3) :
    InBlock ω a₂ a₃ N (WhittakerBlock.archDeriv i j u) := by
  have hspan : WhittakerBlock.archDeriv i j u ∈ Submodule.span ℂ {φ : G3 → ℂ |
      ∃ (w : List (Fin 3 × Fin 3)) (h : G3),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun g => u (g * h)) w} := by
    refine Submodule.subset_span ⟨[(i, j)], 1, ?_⟩
    simp only [List.foldr_cons, List.foldr_nil, mul_one]
  obtain ⟨hsm, -, hc2, hc3⟩ :=
    isArchSmooth3_and_sum_smul_iterate_casimir_eq_zero_of_mem_span_foldr_archDeriv_mul_right u hu.h4
  refine ⟨fun w => ?_, fun γ g => ?_, fun z g => ?_, WhittakerBlock.isArchSmooth3_archDeriv hu.h4 i j,
    kfinite_archDeriv hu.h4 hu.h5 i j, hc2 _ a₂ hu.h6 _ hspan, hc3 _ a₃ hu.h7 _ hspan, fun w => ?_⟩
  · rw [wordFn_archDeriv]; exact hu.h1 _
  · exact archDeriv_mul_left_invariant (fun g => hu.h2 γ g) i j g
  · exact archDeriv_mul_left_char (fun g => hu.h3 z g) i j g
  · rw [wordFn_archDeriv]; exact hu.h8 _

theorem InBlock.word {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {N₂ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ} {N₃ : ℕ}
    {a₃ : Fin (N₃ + 1) → ℂ} {N : ℕ} {u : G3 → ℂ} (hu : InBlock ω a₂ a₃ N u) :
    ∀ w : List (Fin 3 × Fin 3), InBlock ω a₂ a₃ N (wordFn u w)
  | [] => hu
  | p :: w => (InBlock.word hu w).archDeriv p.1 p.2

end Fold0Aux

namespace Fold0Aux

theorem rpow_weaken {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) {a b : ℝ} (hab : a ≤ b) {K t : ℝ}
    (h : t ≤ K * y ^ b) : t ≤ max K 0 * y ^ a := by
  have h1 : y ^ b ≤ y ^ a := Real.rpow_le_rpow_of_exponent_ge hy hy1 hab
  have h2 : K * y ^ b ≤ max K 0 * y ^ b :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _)
  exact h.trans (h2.trans (mul_le_mul_of_nonneg_left h1 (le_max_right _ _)))

theorem injective_pair {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) :
    Function.Injective fun p : Fin n × Fin J => (e p.1, (p.2 : ℕ)) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (he h.1) (Fin.ext h.2)

theorem sum_pair {n J : ℕ} (f : Fin n → Fin J → ℂ) :
    (∑ p : Fin n × Fin J, f p.1 p.2) = ∑ i, ∑ j, f i j := Fintype.sum_prod_type' f

theorem uniq2 {n₁ J₁ n₂ J₂ : ℕ} (e₁ : Fin n₁ → ℂ) (he₁ : Function.Injective e₁) (e₂ : Fin n₂ → ℂ)
    (he₂ : Function.Injective e₂) (c₁ : Fin n₁ → Fin J₁ → ℂ) (c₂ : Fin n₂ → Fin J₂ → ℂ) (θ₁ θ₂ : ℝ)
    (F : ℝ → ℂ)
    (h₁ : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖F y - ∑ i, ∑ j, c₁ i j * ((y : ℂ) ^ e₁ i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ K * y ^ θ₁)
    (h₂ : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖F y - ∑ i, ∑ j, c₂ i j * ((y : ℂ) ^ e₂ i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ K * y ^ θ₂) :
    (∀ (i₁ : Fin n₁) (j₁ : Fin J₁) (i₂ : Fin n₂) (j₂ : Fin J₂), e₁ i₁ = e₂ i₂ → (j₁ : ℕ) = (j₂ : ℕ) →
      (e₁ i₁).re < min θ₁ θ₂ → c₁ i₁ j₁ = c₂ i₂ j₂) ∧
    (∀ (i₂ : Fin n₂) (j₂ : Fin J₂), (e₂ i₂).re < min θ₁ θ₂ →
      (∀ (i₁ : Fin n₁) (j₁ : Fin J₁), ¬ (e₁ i₁ = e₂ i₂ ∧ (j₁ : ℕ) = (j₂ : ℕ))) → c₂ i₂ j₂ = 0) ∧
    (∀ (i₁ : Fin n₁) (j₁ : Fin J₁), (e₁ i₁).re < min θ₁ θ₂ →
      (∀ (i₂ : Fin n₂) (j₂ : Fin J₂), ¬ (e₂ i₂ = e₁ i₁ ∧ (j₂ : ℕ) = (j₁ : ℕ))) → c₁ i₁ j₁ = 0) := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  have H := RegularSingular.expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le
    (fun p : Fin n₁ × Fin J₁ => e₁ p.1) (fun p => (p.2 : ℕ)) (injective_pair e₁ he₁)
    (fun p : Fin n₂ × Fin J₂ => e₂ p.1) (fun p => (p.2 : ℕ)) (injective_pair e₂ he₂)
    (fun p => c₁ p.1 p.2) (fun p => c₂ p.1 p.2) (min θ₁ θ₂) F
    ⟨max K₁ 0, fun y hy hy1 => by
      rw [sum_pair (fun i j => c₁ i j * ((y : ℂ) ^ e₁ i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))]
      exact rpow_weaken hy hy1 (min_le_left _ _) (hK₁ y hy hy1)⟩
    ⟨max K₂ 0, fun y hy hy1 => by
      rw [sum_pair (fun i j => c₂ i j * ((y : ℂ) ^ e₂ i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))]
      exact rpow_weaken hy hy1 (min_le_right _ _) (hK₂ y hy hy1)⟩
  obtain ⟨Heq, H1, H2⟩ := H
  refine ⟨fun i₁ j₁ i₂ j₂ he hj hre => Heq (i₁, j₁) (i₂, j₂) he hj hre, fun i₂ j₂ hre hno => ?_,
    fun i₁ j₁ hre hno => ?_⟩
  · refine H2 (i₂, j₂) hre fun p hp => hno p.1 p.2 ?_
    simp only [Prod.mk.injEq] at hp
    exact ⟨hp.1, hp.2⟩
  · refine H1 (i₁, j₁) hre fun p hp => hno p.1 p.2 ?_
    simp only [Prod.mk.injEq] at hp
    exact ⟨hp.1, hp.2⟩

theorem coeff_zero_of_flat {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (c : Fin n → Fin J → ℂ)
    (θ₁ θ₂ : ℝ) (hre : ∀ i, (e i).re < min θ₁ θ₂) (F : ℝ → ℂ)
    (hflat : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F y‖ ≤ K * y ^ θ₁)
    (hexp : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖F y - ∑ i, ∑ j, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ K * y ^ θ₂) :
    ∀ i j, c i j = 0 := by
  obtain ⟨K₁, hK₁⟩ := hflat
  obtain ⟨K₂, hK₂⟩ := hexp
  intro i j
  have H := expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
    (fun p : Fin n × Fin J => e p.1) (fun p => (p.2 : ℕ)) (fun p => c p.1 p.2) (injective_pair e he)
    (min θ₁ θ₂) F (fun y => F y - ∑ i, ∑ j, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))
    (fun y hy hy1 => by
      rw [sum_pair (fun i j => c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))]; ring)
    ⟨max K₂ 0, fun y hy hy1 => rpow_weaken hy hy1 (min_le_right _ _) (hK₂ y hy hy1)⟩
    ⟨max K₁ 0, fun y hy hy1 => rpow_weaken hy hy1 (min_le_left _ _) (hK₁ y hy hy1)⟩
  exact H (i, j) (hre i)

theorem pi_const_sub_sum {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) (c : ι → ℂ) :
    ((fun _ : Fin 1 => a) - ∑ i, b i • (fun _ : Fin 1 => c i)) = fun _ => a - ∑ i, b i * c i := by
  funext t
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem hasDerivAt_coeff_scalar {ι : Type*} [Fintype ι] (e : ι → ℂ) (n : ι → ℕ)
    (hinj : Function.Injective fun i => (e i, n i)) (θ : ℝ) (hθ : ∀ i, (e i).re < θ)
    (F Fz : ℝ → ℝ → ℂ) (c g : ι → ℝ → ℂ)
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt (fun z => F y z) (Fz y z) z)
    (hFz : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ContinuousOn (fun z => Fz y z) (Set.Ioc 0 2))
    (hg : ∀ i, ContinuousOn (g i) (Set.Ioc 0 2))
    (hexpF : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∃ K : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y z - ∑ i, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ n i) * c i z‖ ≤ K * y ^ θ)
    (hexpFz : ∀ z₀ ∈ Set.Ioc (0 : ℝ) 2, ∃ K ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioc (0 : ℝ) 2, |z - z₀| < ε →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖Fz y z - ∑ i, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ n i) * g i z‖ ≤ K * y ^ θ) :
    ∀ i, ∀ z ∈ Set.Ioo (0 : ℝ) 2, HasDerivAt (c i) (g i z) z := by
  have H := RegularSingular.hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le 1 e n hinj θ hθ
    (fun y z _ => F y z) (fun y z _ => Fz y z) (fun i z _ => c i z) (fun i z _ => g i z)
    (fun y hy z hz => hasDerivAt_pi.2 fun _ => hF y hy z hz)
    (fun y hy => continuousOn_pi.2 fun _ => hFz y hy)
    (fun i => continuousOn_pi.2 fun _ => hg i)
    (fun z hz => by
      obtain ⟨K, hK⟩ := hexpF z hz
      refine ⟨K, fun y hy => ?_⟩
      rw [pi_const_sub_sum, pi_norm_const]
      exact hK y hy)
    (fun z₀ hz₀ => by
      obtain ⟨K, ε, hε, hK⟩ := hexpFz z₀ hz₀
      refine ⟨K, ε, hε, fun z hz hzz y hy => ?_⟩
      rw [pi_const_sub_sum, pi_norm_const]
      exact hK z hz hzz y hy)
  intro i z hz
  exact (hasDerivAt_pi.1 (H i z hz)) 0

end Fold0Aux

namespace Fold0Aux

abbrev unip (p q : Fin 3) (r : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = p ∧ b = q then r else 0

noncomputable abbrev Acur (p q : Fin 3) (r : ℝ) : G3 := WhittakerBlock.archRealLift3 (unip p q r)

noncomputable abbrev γf (p q : Fin 3) (r : ℝ) : ℂ := (((1 + if p = q then r else 0)⁻¹ : ℝ) : ℂ)

theorem one_add_ite_pos {p q : Fin 3} {r : ℝ} (hr : -1 < r) : 0 < 1 + (if p = q then r else 0) := by
  split_ifs <;> linarith

theorem det_unip (p q : Fin 3) (r : ℝ) : (Matrix.of (unip p q r)).det = 1 + if p = q then r else 0 := by
  fin_cases p <;> fin_cases q <;> simp [unip, Matrix.det_fin_three]

theorem det_unip_ne {p q : Fin 3} {r : ℝ} (hr : -1 < r) : (Matrix.of (unip p q r)).det ≠ 0 := by
  rw [det_unip]; exact (one_add_ite_pos hr).ne'

theorem continuous_unip (p q : Fin 3) : Continuous (unip p q) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  refine continuous_const.add ?_
  by_cases h : a = p ∧ b = q
  · simp only [h, and_self, if_true]; exact continuous_id
  · simp only [h, if_false]; exact continuous_const

theorem continuous_one_add_ite (p q : Fin 3) : Continuous fun r : ℝ => 1 + (if p = q then r else 0) := by
  by_cases h : p = q
  · simp only [h, if_true]; exact continuous_const.add continuous_id
  · simp only [h, if_false]; exact continuous_const

theorem continuousOn_Acur (p q : Fin 3) : ContinuousOn (Acur p q) (Set.Ioi (-1)) := by
  refine A7Port.continuousOn_archRealLift3_detSet.comp (continuous_unip p q).continuousOn ?_
  intro r hr
  exact det_unip_ne hr

theorem continuousOn_γf (p q : Fin 3) : ContinuousOn (γf p q) (Set.Ioi (-1)) :=
  Complex.continuous_ofReal.comp_continuousOn
    ((continuous_one_add_ite p q).continuousOn.inv₀ fun r hr => (one_add_ite_pos hr).ne')

theorem norm_γf_le {p q : Fin 3} {r m : ℝ} (hm : 0 < m) (hr : m ≤ 1 + (if p = q then r else 0)) :
    ‖γf p q r‖ ≤ m⁻¹ := by
  have hpos : 0 < 1 + (if p = q then r else 0) := hm.trans_le hr
  rw [show γf p q r = (((1 + if p = q then r else 0)⁻¹ : ℝ) : ℂ) from rfl, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  exact inv_anti₀ hm hr

theorem γf_zero (p q : Fin 3) : γf p q 0 = 1 := by
  simp

theorem exists_band {z : ℝ} (hz : 0 < z) : ∃ b : ℝ, 1 ≤ b ∧ b⁻¹ ≤ z ∧ z ≤ b := by
  refine ⟨max z z⁻¹, ?_, ?_, le_max_left _ _⟩
  · rcases le_or_gt 1 z with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_le_inv₀ hz).2 h.le)
  · have := inv_anti₀ (inv_pos.2 hz) (le_max_right z z⁻¹)
    rwa [inv_inv] at this

theorem wh_smooth {v : G3 → ℂ} (hv1 : ∀ w, Continuous (wordFn v w)) (hv4 : WhittakerBlock.IsArchSmooth3 v)
    (p q : Fin 3) :
    WhittakerBlock.IsArchSmooth3 (Wh v) ∧ Wh (WhittakerBlock.archDeriv p q v) = WhittakerBlock.archDeriv p q (Wh v) := by
  obtain ⟨h1, h2⟩ := whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 v hv4 hv1
  refine ⟨h2, ?_⟩
  have := h1 [(p, q)]
  simpa only [List.foldr_cons, List.foldr_nil] using this

theorem flow_hasDerivAt {v : G3 → ℂ} (hv1 : ∀ w, Continuous (wordFn v w)) (hv4 : WhittakerBlock.IsArchSmooth3 v)
    (p q : Fin 3) (x : G3) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => Wh v (x * Acur p q (s - 1)))
      (γf p q (s - 1) * Wh (WhittakerBlock.archDeriv p q v) (x * Acur p q (s - 1))) s := by
  obtain ⟨hW4, hWX⟩ := wh_smooth hv1 hv4 p q
  have hne : 1 + (if p = q then s - 1 else 0) ≠ 0 := (one_add_ite_pos (by linarith)).ne'
  have h0 := WhittakerBlock.hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3 (Wh v) hW4 x p q (s - 1) hne
  rw [← hWX] at h0
  have h1 := h0.scomp s ((hasDerivAt_id s).sub_const 1)
  rw [one_smul] at h1
  exact h1

theorem level1 {ρ δ9 : ℝ} (hδ9 : 0 < δ9) {n9 J9 : ℕ} {e9 : Fin n9 → ℂ} (he9 : Function.Injective e9)
    (hre9 : ∀ i, (e9 i).re ≤ ρ) {v : G3 → ℂ} (hv1 : ∀ w, Continuous (wordFn v w))
    (hv4 : WhittakerBlock.IsArchSmooth3 v) (p q : Fin 3)
    {c d : Fin n9 → Fin J9 → ℝ → G3 → ℂ}
    (hc1 : ∀ K : Set G3, IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K, ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b →
      ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖Wh v (tor y₁ y₂ * k) - ∑ i, ∑ j, c i j y₂ k * ((y₁ : ℂ) ^ e9 i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C * y₁ ^ (ρ + δ9))
    (hdc : ∀ i j, ContinuousOn (fun x : ℝ × G3 => d i j x.1 x.2) {x | 0 < x.1})
    (hd1 : ∀ K : Set G3, IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K, ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b →
      ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖Wh (WhittakerBlock.archDeriv p q v) (tor y₁ y₂ * k) -
            ∑ i, ∑ j, d i j y₂ k * ((y₁ : ℂ) ^ e9 i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * y₁ ^ (ρ + δ9))
    (z : ℝ) (hz : 0 < z) (k : G3) (i : Fin n9) (j : Fin J9) :
    ∀ r ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => c i j z (k * Acur p q r)) (γf p q r * d i j z (k * Acur p q r)) r := by
  obtain ⟨b, hb, hbz, hzb⟩ := exists_band hz
  have hXcont : Continuous (Wh (WhittakerBlock.archDeriv p q v)) :=
    A7Port.continuous_whittaker3_of_continuous (hv1 [(p, q)])

  have hpath0 : ContinuousOn (fun s : ℝ => k * Acur p q (s - 1)) (Set.Ioi 0) := by
    refine continuousOn_const.mul ((continuousOn_Acur p q).comp (continuous_id.sub continuous_const).continuousOn ?_)
    intro s hs
    simp only [Set.mem_Ioi] at hs ⊢
    linarith
  have hpath : ContinuousOn (fun s : ℝ => tor 0 z * 1 * (k * Acur p q (s - 1))) (Set.Ioi 0) :=
    continuousOn_const.mul hpath0
  have hγ : ContinuousOn (fun s : ℝ => γf p q (s - 1)) (Set.Ioi 0) := by
    refine (continuousOn_γf p q).comp (continuous_id.sub continuous_const).continuousOn ?_
    intro s hs
    simp only [Set.mem_Ioi] at hs ⊢
    linarith
  have H := hasDerivAt_coeff_scalar (ι := Fin n9 × Fin J9) (fun ij => e9 ij.1) (fun ij => (ij.2 : ℕ))
    (injective_pair e9 he9) (ρ + δ9) (fun ij => by have := hre9 ij.1; linarith)
    (fun y s => Wh v (tor y z * (k * Acur p q (s - 1))))
    (fun y s => γf p q (s - 1) * Wh (WhittakerBlock.archDeriv p q v) (tor y z * (k * Acur p q (s - 1))))
    (fun ij s => c ij.1 ij.2 z (k * Acur p q (s - 1)))
    (fun ij s => γf p q (s - 1) * d ij.1 ij.2 z (k * Acur p q (s - 1)))
    (fun y hy s hs => flow_hasDerivAt hv1 hv4 p q (tor y z * k |> fun x => x) hs.1 |> fun h => by
      simpa only [mul_assoc] using h)
    (fun y hy => by
      refine (hγ.mul (hXcont.comp_continuousOn (continuousOn_const.mul hpath0))).mono ?_
      exact fun s hs => hs.1)
    (fun ij => by
      refine (hγ.mul ((hdc ij.1 ij.2).comp (continuousOn_const.prodMk hpath0) ?_)).mono fun s hs => hs.1
      intro s hs
      exact hz)
    (fun s hs => by
      obtain ⟨C, hC⟩ := hc1 {k * Acur p q (s - 1)} isCompact_singleton b hb
      refine ⟨C, fun y hy => ?_⟩
      have := hC _ (Set.mem_singleton _) z hbz hzb y hy.1 hy.2
      rw [← sum_pair (fun i j => c i j z (k * Acur p q (s - 1)) *
        ((y : ℂ) ^ e9 i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))] at this
      simpa only [mul_comm (c _ _ _ _)] using this)
    (fun s₀ hs₀ => by

      set I : Set ℝ := Set.Icc (s₀ / 2 - 1) (3 * s₀ / 2 - 1)
      have hIsub : I ⊆ Set.Ioi (-1) := fun r hr => by
        simp only [Set.mem_Ioi]; have := hr.1; have := hs₀.1; linarith
      have hK : IsCompact ((fun r => k * Acur p q r) '' I) :=
        isCompact_Icc.image_of_continuousOn ((continuousOn_const.mul (continuousOn_Acur p q)).mono hIsub)
      obtain ⟨C, hC⟩ := hd1 _ hK b hb
      refine ⟨2 / s₀ * max C 0, s₀ / 2, by linarith [hs₀.1], fun s hs hss y hy => ?_⟩
      have hsI : s - 1 ∈ I := by
        rw [abs_lt] at hss
        exact ⟨by linarith, by linarith⟩
      have hmem : k * Acur p q (s - 1) ∈ (fun r => k * Acur p q r) '' I := ⟨s - 1, hsI, rfl⟩
      have h1 := hC _ hmem z hbz hzb y hy.1 hy.2
      have h2 : ‖Wh (WhittakerBlock.archDeriv p q v) (tor y z * (k * Acur p q (s - 1))) -
          ∑ ij : Fin n9 × Fin J9, ((y : ℂ) ^ e9 ij.1 * ((Real.log y : ℝ) : ℂ) ^ (ij.2 : ℕ)) *
            d ij.1 ij.2 z (k * Acur p q (s - 1))‖ ≤ max C 0 * y ^ (ρ + δ9) := by
        rw [← sum_pair (fun i j => d i j z (k * Acur p q (s - 1)) *
          ((y : ℂ) ^ e9 i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))] at h1
        simp only [mul_comm (d _ _ _ _)] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.1.le _))
      have hγb : ‖γf p q (s - 1)‖ ≤ (s₀ / 2)⁻¹ := by
        refine norm_γf_le (by linarith [hs₀.1]) ?_
        rw [abs_lt] at hss
        split_ifs <;> linarith [hs₀.2]
      have hfac : γf p q (s - 1) * Wh (WhittakerBlock.archDeriv p q v) (tor y z * (k * Acur p q (s - 1))) -
          ∑ ij : Fin n9 × Fin J9, ((y : ℂ) ^ e9 ij.1 * ((Real.log y : ℝ) : ℂ) ^ (ij.2 : ℕ)) *
            (γf p q (s - 1) * d ij.1 ij.2 z (k * Acur p q (s - 1))) =
          γf p q (s - 1) * (Wh (WhittakerBlock.archDeriv p q v) (tor y z * (k * Acur p q (s - 1))) -
            ∑ ij : Fin n9 × Fin J9, ((y : ℂ) ^ e9 ij.1 * ((Real.log y : ℝ) : ℂ) ^ (ij.2 : ℕ)) *
              d ij.1 ij.2 z (k * Acur p q (s - 1))) := by
        rw [mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun ij _ => ?_
        ring
      rw [hfac, norm_mul]
      calc ‖γf p q (s - 1)‖ * _ ≤ (s₀ / 2)⁻¹ * (max C 0 * y ^ (ρ + δ9)) :=
            mul_le_mul hγb h2 (norm_nonneg _) (inv_nonneg.2 (by linarith [hs₀.1]))
        _ = 2 / s₀ * max C 0 * y ^ (ρ + δ9) := by rw [inv_div]; ring)
  intro r hr
  have H1 := H (i, j) (r + 1) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have H2 := H1.comp_add_const r 1
  simp only [add_sub_cancel_right] at H2
  exact H2

end Fold0Aux

namespace Fold0Aux

theorem level2 {ρ δ9 : ℝ} (hδ9 : 0 < δ9) {n9 J9 : ℕ} {e9 : Fin n9 → ℂ} (he9 : Function.Injective e9)
    (hre9 : ∀ i, (e9 i).re ≤ ρ) (p q : Fin 3)
    {c d : Fin n9 → Fin J9 → ℝ → G3 → ℂ} {c' d' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ}
    (hL1 : ∀ z : ℝ, 0 < z → ∀ (k : G3) (i : Fin n9) (j : Fin J9), ∀ r ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => c i j z (k * Acur p q r)) (γf p q r * d i j z (k * Acur p q r)) r)
    (hdc : ∀ i j, ContinuousOn (fun x : ℝ × G3 => d i j x.1 x.2) {x | 0 < x.1})
    (hc2 : ∀ K : Set G3, IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n9) (j : Fin J9), ∀ y₂ : ℝ, 0 < y₂ →
      y₂ ≤ 1 → ‖c i j y₂ k - ∑ i', ∑ j', c' i j i' j' k *
        ((y₂ : ℂ) ^ e9 i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ9))
    (hd'c : ∀ i j i' j', Continuous (d' i j i' j'))
    (hd2 : ∀ K : Set G3, IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n9) (j : Fin J9), ∀ y₂ : ℝ, 0 < y₂ →
      y₂ ≤ 1 → ‖d i j y₂ k - ∑ i', ∑ j', d' i j i' j' k *
        ((y₂ : ℂ) ^ e9 i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ9))
    (k : G3) (i : Fin n9) (j : Fin J9) (hzero : ∀ (i' : Fin n9) (j' : Fin J9) (k' : G3), c' i j i' j' k' = 0) :
    ∀ (i' : Fin n9) (j' : Fin J9), d' i j i' j' k = 0 := by
  set k₀ : G3 := k * (Acur p q 0)⁻¹ with hk₀
  have hk₀A : k₀ * Acur p q 0 = k := by rw [hk₀]; exact inv_mul_cancel_right k _
  have haff : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (s - 1) / 2) (1 / 2 : ℝ) s := fun s =>
    ((hasDerivAt_id s).sub_const 1).div_const 2
  have haffc : Continuous fun s : ℝ => (s - 1) / 2 := (continuous_id.sub continuous_const).div_const 2
  have hmaps : Set.MapsTo (fun s : ℝ => (s - 1) / 2) (Set.Ioi 0) (Set.Ioi (-1)) := by
    intro s hs; simp only [Set.mem_Ioi] at hs ⊢; linarith
  have hpath0 : ContinuousOn (fun s : ℝ => k₀ * Acur p q ((s - 1) / 2)) (Set.Ioi 0) :=
    continuousOn_const.mul ((continuousOn_Acur p q).comp haffc.continuousOn hmaps)
  have hγ : ContinuousOn (fun s : ℝ => γf p q ((s - 1) / 2)) (Set.Ioi 0) :=
    (continuousOn_γf p q).comp haffc.continuousOn hmaps

  set I : Set ℝ := Set.Icc (-1 / 2) (1 / 2)
  have hIsub : I ⊆ Set.Ioi (-1) := fun r hr => by simp only [Set.mem_Ioi]; have := hr.1; linarith
  have hK : IsCompact ((fun r => k₀ * Acur p q r) '' I) :=
    isCompact_Icc.image_of_continuousOn ((continuousOn_const.mul (continuousOn_Acur p q)).mono hIsub)
  obtain ⟨C₂, hC₂⟩ := hd2 _ hK
  have H := hasDerivAt_coeff_scalar (ι := Fin n9 × Fin J9) (fun ij => e9 ij.1) (fun ij => (ij.2 : ℕ))
    (injective_pair e9 he9) (ρ + δ9) (fun ij => by have := hre9 ij.1; linarith)
    (fun z s => c i j z (k₀ * Acur p q ((s - 1) / 2)))
    (fun z s => (1 / 2 : ℝ) • (γf p q ((s - 1) / 2) * d i j z (k₀ * Acur p q ((s - 1) / 2))))
    (fun ij s => c' i j ij.1 ij.2 (k₀ * Acur p q ((s - 1) / 2)))
    (fun ij s => (1 / 2 : ℝ) • (γf p q ((s - 1) / 2) * d' i j ij.1 ij.2 (k₀ * Acur p q ((s - 1) / 2))))
    (fun z hz s hs => by
      have hr : (s - 1) / 2 ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have := (hL1 z hz.1 k₀ i j ((s - 1) / 2) hr).scomp s (haff s)
      exact this)
    (fun z hz => by
      refine ((hγ.mul ((hdc i j).comp (continuousOn_const.prodMk hpath0) fun s hs => hz.1)).const_smul
        (1 / 2 : ℝ)).mono fun s hs => hs.1)
    (fun ij => by
      refine ((hγ.mul ((hd'c i j ij.1 ij.2).comp_continuousOn hpath0)).const_smul (1 / 2 : ℝ)).mono
        fun s hs => hs.1)
    (fun s hs => by
      obtain ⟨C, hC⟩ := hc2 {k₀ * Acur p q ((s - 1) / 2)} isCompact_singleton
      refine ⟨C, fun z hz => ?_⟩
      have := hC _ (Set.mem_singleton _) i j z hz.1 hz.2
      rw [← sum_pair (fun i' j' => c' i j i' j' (k₀ * Acur p q ((s - 1) / 2)) *
        ((z : ℂ) ^ e9 i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)))] at this
      simpa only [mul_comm (c' _ _ _ _ _)] using this)
    (fun s₀ hs₀ => by
      refine ⟨max C₂ 0, 1, one_pos, fun s hs hss z hz => ?_⟩
      have hsI : (s - 1) / 2 ∈ I := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hmem : k₀ * Acur p q ((s - 1) / 2) ∈ (fun r => k₀ * Acur p q r) '' I := ⟨(s - 1) / 2, hsI, rfl⟩
      have h1 := hC₂ _ hmem i j z hz.1 hz.2
      rw [← sum_pair (fun i' j' => d' i j i' j' (k₀ * Acur p q ((s - 1) / 2)) *
        ((z : ℂ) ^ e9 i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)))] at h1
      simp only [mul_comm (d' _ _ _ _ _)] at h1
      have h2 := h1.trans (mul_le_mul_of_nonneg_right (le_max_left C₂ 0) (Real.rpow_nonneg hz.1.le _))
      have hγb : ‖γf p q ((s - 1) / 2)‖ ≤ (1 / 2 : ℝ)⁻¹ := by
        refine norm_γf_le (by norm_num) ?_
        split_ifs <;> linarith [hs.1]
      have hfac : (1 / 2 : ℝ) • (γf p q ((s - 1) / 2) * d i j z (k₀ * Acur p q ((s - 1) / 2))) -
          ∑ ij : Fin n9 × Fin J9, ((z : ℂ) ^ e9 ij.1 * ((Real.log z : ℝ) : ℂ) ^ (ij.2 : ℕ)) *
            ((1 / 2 : ℝ) • (γf p q ((s - 1) / 2) * d' i j ij.1 ij.2 (k₀ * Acur p q ((s - 1) / 2)))) =
          (1 / 2 : ℝ) • (γf p q ((s - 1) / 2) * (d i j z (k₀ * Acur p q ((s - 1) / 2)) -
            ∑ ij : Fin n9 × Fin J9, ((z : ℂ) ^ e9 ij.1 * ((Real.log z : ℝ) : ℂ) ^ (ij.2 : ℕ)) *
              d' i j ij.1 ij.2 (k₀ * Acur p q ((s - 1) / 2)))) := by
        rw [mul_sub, Finset.mul_sum, smul_sub, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun ij _ => ?_
        simp only [Complex.real_smul]
        ring
      rw [hfac, norm_smul, norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc (1 / 2 : ℝ) * (‖γf p q ((s - 1) / 2)‖ * _) ≤ (1 / 2) * ((1 / 2 : ℝ)⁻¹ * (max C₂ 0 * z ^ (ρ + δ9))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hγb h2 (norm_nonneg _) (by positivity)) (by norm_num)
        _ = max C₂ 0 * z ^ (ρ + δ9) := by ring)
  intro i' j'
  have H1 := H (i', j') 1 ⟨one_pos, one_lt_two⟩
  have hf : (fun s : ℝ => c' i j i' j' (k₀ * Acur p q ((s - 1) / 2))) = fun _ => (0 : ℂ) :=
    funext fun s => hzero _ _ _
  simp only [hf] at H1
  have h0 := H1.unique (hasDerivAt_const (1 : ℝ) (0 : ℂ))
  rw [sub_self, zero_div, γf_zero, one_mul, hk₀A, smul_eq_zero] at h0
  rcases h0 with h | h
  · norm_num at h
  · exact h

theorem lead_step {n9 J9 : ℕ} (p q : Fin 3) {c d : Fin n9 → Fin J9 → ℝ → G3 → ℂ}
    (hL1 : ∀ z : ℝ, 0 < z → ∀ (k : G3) (i : Fin n9) (j : Fin J9), ∀ r ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => c i j z (k * Acur p q r)) (γf p q r * d i j z (k * Acur p q r)) r)
    (z : ℝ) (hz : 0 < z) (k : G3) (i : Fin n9) (j : Fin J9) (hzero : ∀ k' : G3, c i j z k' = 0) :
    d i j z k = 0 := by
  set k₀ : G3 := k * (Acur p q 0)⁻¹ with hk₀
  have hk₀A : k₀ * Acur p q 0 = k := by rw [hk₀]; exact inv_mul_cancel_right k _
  have H1 := hL1 z hz k₀ i j 0 ⟨by norm_num, by norm_num⟩
  have hf : (fun r : ℝ => c i j z (k₀ * Acur p q r)) = fun _ => (0 : ℂ) := funext fun s => hzero _
  simp only [hf] at H1
  have h0 := H1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  rw [γf_zero, one_mul, hk₀A] at h0
  exact h0

structure Spec (ρ δ9 : ℝ) {n9 J9 : ℕ} (e9 : Fin n9 → ℂ) (v : G3 → ℂ) (c : Fin n9 → Fin J9 → ℝ → G3 → ℂ)
    (c' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ) : Prop where
  cont : ∀ i j, ContinuousOn (fun x : ℝ × G3 => c i j x.1 x.2) {x | 0 < x.1}
  exp1 : ∀ K : Set G3, IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K, ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b →
    ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
      ‖Wh v (tor y₁ y₂ * k) - ∑ i, ∑ j, c i j y₂ k * ((y₁ : ℂ) ^ e9 i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        C * y₁ ^ (ρ + δ9)
  cont' : ∀ i j i' j', Continuous (c' i j i' j')
  exp2 : ∀ K : Set G3, IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n9) (j : Fin J9), ∀ y₂ : ℝ, 0 < y₂ →
    y₂ ≤ 1 → ‖c i j y₂ k - ∑ i', ∑ j', c' i j i' j' k *
      ((y₂ : ℂ) ^ e9 i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ9)

def Claim {n9 J9 : ℕ} (e9 : Fin n9 → ℂ) (ℓ : ℂ) (jj : ℕ) (c : Fin n9 → Fin J9 → ℝ → G3 → ℂ)
    (c' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ) : Prop :=
  (∀ i9 : Fin n9, (e9 i9).re < ℓ.re → ∀ (j9 : Fin J9) (k : G3) (z : ℝ), 0 < z → c i9 j9 z k = 0) ∧
  (∀ i9 : Fin n9, e9 i9 = ℓ → ∀ j9 : Fin J9, jj ≤ (j9 : ℕ) →
    ∀ (i' : Fin n9) (j' : Fin J9) (k : G3), c' i9 j9 i' j' k = 0)

theorem claim_step {ρ δ9 : ℝ} (hδ9 : 0 < δ9) {n9 J9 : ℕ} {e9 : Fin n9 → ℂ} (he9 : Function.Injective e9)
    (hre9 : ∀ i, (e9 i).re ≤ ρ) {v : G3 → ℂ} (hv1 : ∀ w, Continuous (wordFn v w))
    (hv4 : WhittakerBlock.IsArchSmooth3 v) (p q : Fin 3)
    {c d : Fin n9 → Fin J9 → ℝ → G3 → ℂ} {c' d' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ}
    (S : Spec ρ δ9 e9 v c c') (T : Spec ρ δ9 e9 (WhittakerBlock.archDeriv p q v) d d') {ℓ : ℂ} {jj : ℕ}
    (h : Claim e9 ℓ jj c c') : Claim e9 ℓ jj d d' := by
  have hL1 : ∀ z : ℝ, 0 < z → ∀ (k : G3) (i : Fin n9) (j : Fin J9), ∀ r ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => c i j z (k * Acur p q r)) (γf p q r * d i j z (k * Acur p q r)) r :=
    fun z hz k i j => level1 hδ9 he9 hre9 hv1 hv4 p q S.exp1 T.cont T.exp1 z hz k i j
  refine ⟨fun i9 hi9 j9 k z hz => ?_, fun i9 hi9 j9 hj9 i' j' k => ?_⟩
  · exact lead_step p q hL1 z hz k i9 j9 fun k' => h.1 i9 hi9 j9 k' z hz
  · exact level2 hδ9 he9 hre9 p q hL1 T.cont S.exp2 T.cont' T.exp2 k i9 j9
      (fun i'' j'' k' => h.2 i9 hi9 j9 hj9 i'' j'' k') i' j'

theorem claim_words {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {N₂ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ} {N₃ : ℕ}
    {a₃ : Fin (N₃ + 1) → ℂ} {N : ℕ} {u : G3 → ℂ} (hu : InBlock ω a₂ a₃ N u)
    {ρ δ9 : ℝ} (hδ9 : 0 < δ9) {n9 J9 : ℕ} {e9 : Fin n9 → ℂ} (he9 : Function.Injective e9)
    (hre9 : ∀ i, (e9 i).re ≤ ρ)
    (HS : ∀ v : G3 → ℂ, InBlock ω a₂ a₃ N v → ∃ (c : Fin n9 → Fin J9 → ℝ → G3 → ℂ)
      (c' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ), Spec ρ δ9 e9 v c c') {ℓ : ℂ} {jj : ℕ}
    (hbase : ∀ (c : Fin n9 → Fin J9 → ℝ → G3 → ℂ) (c' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ),
      Spec ρ δ9 e9 u c c' → Claim e9 ℓ jj c c') :
    ∀ (w : List (Fin 3 × Fin 3)) (c : Fin n9 → Fin J9 → ℝ → G3 → ℂ)
      (c' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ), Spec ρ δ9 e9 (wordFn u w) c c' → Claim e9 ℓ jj c c'
  | [] => hbase
  | p :: w => fun c c' T => by
      obtain ⟨c₀, c₀', S⟩ := HS _ (hu.word w)
      exact claim_step hδ9 he9 hre9 (hu.word w).h1 (hu.word w).h4 p.1 p.2 S T
        (claim_words hu hδ9 he9 hre9 HS hbase w c₀ c₀' S)

end Fold0Aux

namespace Fold0Aux

theorem mul_mem_slab {Z s : ℝ} (hZ : 1 ≤ Z) (hs0 : 0 < s) (hs2 : s ≤ 2) : Z * s ∈ Set.Ioc (0 : ℝ) (2 * Z) := by
  refine ⟨mul_pos (by linarith) hs0, ?_⟩
  calc Z * s ≤ Z * 2 := mul_le_mul_of_nonneg_left hs2 (by linarith)
    _ = 2 * Z := mul_comm _ _

theorem claim_base {ρ δ δ9 : ℝ} (hδ : 0 < δ) (hδ9 : 0 < δ9) {n J n9 J9 : ℕ} {e : Fin n → ℂ}
    (he : Function.Injective e) (hre : ∀ i, (e i).re ≤ ρ) {e9 : Fin n9 → ℂ} (he9 : Function.Injective e9)
    (hre9 : ∀ i, (e9 i).re ≤ ρ) {u : G3 → ℂ} {c : Fin n → Fin J → ℝ → G3 → ℂ}
    (hC : ∀ K : Set G3, IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K, ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b →
      ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖Wh u (tor y₁ y₂ * k) - ∑ i, ∑ j, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C * y₁ ^ (ρ + δ))
    (i : Fin n) (j : Fin J)
    (hlead : ∀ (k : G3) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re → ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0)
    (hflat : ∀ j' : Fin J, j ≤ j' → ∀ K : Set G3, IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
      ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j' y₂ k‖ ≤ C * y₂ ^ (ρ + δ))
    {c9 : Fin n9 → Fin J9 → ℝ → G3 → ℂ} {c9' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ}
    (S : Spec ρ δ9 e9 u c9 c9') : Claim e9 (e i) (j : ℕ) c9 c9' := by

  have ident : ∀ z : ℝ, 0 < z → ∀ k : G3,
      (∀ (i'' : Fin n) (j'' : Fin J) (i9 : Fin n9) (j9 : Fin J9), e i'' = e9 i9 → (j'' : ℕ) = (j9 : ℕ) →
        c i'' j'' z k = c9 i9 j9 z k) ∧
      (∀ (i9 : Fin n9) (j9 : Fin J9), (∀ (i'' : Fin n) (j'' : Fin J), ¬ (e i'' = e9 i9 ∧ (j'' : ℕ) = (j9 : ℕ))) →
        c9 i9 j9 z k = 0) := by
    intro z hz k
    obtain ⟨b, hb, hbz, hzb⟩ := exists_band hz
    obtain ⟨C₁, hC₁⟩ := hC {k} isCompact_singleton b hb
    obtain ⟨C₂, hC₂⟩ := S.exp1 {k} isCompact_singleton b hb
    have U := uniq2 e he e9 he9 (fun i'' j'' => c i'' j'' z k) (fun i9 j9 => c9 i9 j9 z k) (ρ + δ) (ρ + δ9)
      (fun y => Wh u (tor y z * k))
      ⟨C₁, fun y hy hy1 => hC₁ k rfl z hbz hzb y hy hy1⟩ ⟨C₂, fun y hy hy1 => hC₂ k rfl z hbz hzb y hy hy1⟩
    refine ⟨fun i'' j'' i9 j9 h1 h2 => U.1 i'' j'' i9 j9 h1 h2 ?_, fun i9 j9 hno => U.2.1 i9 j9 ?_ hno⟩
    · have := hre i''; rw [lt_min_iff]; constructor <;> linarith
    · have := hre9 i9; rw [lt_min_iff]; constructor <;> linarith
  refine ⟨fun i9 hi9 j9 k z hz => ?_, fun i9 hi9 j9 hj9 i' j' k => ?_⟩
  · by_cases hex : ∃ (i'' : Fin n) (j'' : Fin J), e i'' = e9 i9 ∧ (j'' : ℕ) = (j9 : ℕ)
    · obtain ⟨i'', j'', h1, h2⟩ := hex
      rw [← (ident z hz k).1 i'' j'' i9 j9 h1 h2]
      exact hlead k i'' j'' (by rw [h1]; exact hi9) z hz
    · push Not at hex
      exact (ident z hz k).2 i9 j9 fun i'' j'' h => hex i'' j'' h.1 h.2
  · obtain ⟨C₂, hC₂⟩ := S.exp2 {k} isCompact_singleton
    refine coeff_zero_of_flat e9 he9 (fun i' j' => c9' i9 j9 i' j' k) (ρ + δ) (ρ + δ9)
      (fun i' => by have := hre9 i'; rw [lt_min_iff]; constructor <;> linarith) (fun y => c9 i9 j9 y k) ?_
      ⟨C₂, fun y hy hy1 => hC₂ k rfl i9 j9 y hy hy1⟩ i' j'
    by_cases hJ : (j9 : ℕ) < J
    · obtain ⟨C, hC'⟩ := hflat ⟨j9, hJ⟩ (Fin.le_def.2 (by simpa using hj9)) {k} isCompact_singleton
      refine ⟨C, fun y hy hy1 => ?_⟩
      show ‖c9 i9 j9 y k‖ ≤ _
      rw [← (ident y hy k).1 i ⟨j9, hJ⟩ i9 j9 hi9.symm rfl]
      exact hC' k rfl y hy hy1
    · refine ⟨0, fun y hy hy1 => ?_⟩
      show ‖c9 i9 j9 y k‖ ≤ _
      rw [(ident y hy k).2 i9 j9 ?_]
      · simp
      · rintro i'' j'' ⟨h1, h2⟩
        exact hJ (h2 ▸ j''.isLt)

end Fold0Aux

open Fold0Aux in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∃ ρ₀ : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ → Function.Injective e →
      (∀ i, (e i).re ≤ ρ) →
      ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      ∀ (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) →
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) →
        ∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ j' : Fin J, j ≤ j' →
              (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
              ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j' y₂ k‖ ≤ C * y₂ ^ (ρ + δ))) →
            ∀ (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ), archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
              ∀ (j' : Fin J), j ≤ j' → ∀ (Z : ℝ), 1 ≤ Z →
                ∃ (R d : ℕ) (Mm : Matrix (Fin R) (Fin R) ℂ) (A : Fin d → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
                  (q : Polynomial ℂ) (σ B : ℝ) (V V' : ℝ → (Fin R → ℂ)) (a₀ : Fin R),
                  q ≠ 0 ∧ Polynomial.aeval Mm q = 0 ∧ (∀ x : ℂ, q.IsRoot x → x.re < σ) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt V (V' s) s ∧
                    (s : ℂ) • V' s = (fun a => ∑ b, Mm a b • V s b) +
                      ∑ k : Fin d, ((s : ℂ) ^ ((k : ℕ) + 1)) • A k (V s)) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖V s‖ ≤ B * s ^ σ) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, V s a₀ = c i j' (Z * s) g₀) := by
  classical

  obtain ⟨d, d₂, d', d₂', hS1⟩ := LanglandsTunnell.CubicInduction.exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le N₂ N₃
  obtain ⟨_ι, _ι', q, q', hq, hq', _hdq, _hdq', _hrq, _hrq', hsysU⟩ := hS1 ω a₂ ha₂ a₃ ha₃
  clear hS1

  refine ⟨∑ x ∈ q'.roots.toFinset, |x.re|, ?_⟩
  intro ρ hρ n J e δ hδ hinj hre N u h1 h2 h3 h4 h5 h6 h7 h8 c hc hC i j hlead hflat g₀ hg₀ j' hjj' Z hZ
  have hroots : ∀ x : ℂ, q'.IsRoot x → x.re ≤ ρ := by
    intro x hx
    have hmem : x ∈ q'.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hq']; exact hx
    have h1' : |x.re| ≤ ∑ x ∈ q'.roots.toFinset, |x.re| :=
      Finset.single_le_sum (f := fun x : ℂ => |x.re|) (fun _ _ => abs_nonneg _) hmem
    linarith [le_abs_self x.re]
  obtain ⟨r, w, κf, Mc, Mc', A, A', hw0, hκ0, hκf, hMc, hMc', hA, hA', hsysg⟩ := hsysU u h1 h2 h3 h4 h5 h6 h7
  clear hsysU
  have hZ0 : 0 < Z := by linarith

  obtain ⟨nS, eS, δS, hδS, heS, hreS, hcov, hgap, hgap', hmem⟩ := A7Port.family_of_polys q q' hq hq' ρ
  obtain ⟨D, _hD, hE⟩ := RegularSingular.exists_logDepth_le_natDegree_norm_sub_expansion_le.{0, 0} q hq
  have hcl : ∀ (i : Fin nS) (k : ℕ), (eS i + k).re ≤ ρ → ∃ i', eS i' = eS i + k := by
    intro i k hk
    obtain ⟨e₀, he₀, m, hm⟩ := hmem i
    have hshift : eS i + k = e₀ + ((m + k : ℕ) : ℂ) := by rw [hm]; push_cast; ring
    refine hcov (eS i + k) ?_ hk
    rcases he₀ with h | h
    · exact Or.inl ⟨e₀, h, m + k, hshift⟩
    · exact Or.inr ⟨e₀, h, m + k, hshift⟩
  have hgapF : ∀ (i : Fin nS) (k : ℕ), ρ < (eS i + k).re → ρ + 2 * δS ≤ (eS i + k).re := by
    intro i k hk
    obtain ⟨e₀, he₀, m, hm⟩ := hmem i
    have hshift : eS i + k = e₀ + ((m + k : ℕ) : ℂ) := by rw [hm]; push_cast; ring
    rw [hshift] at hk ⊢
    rcases he₀ with h | h
    · exact hgap e₀ h (m + k) hk
    · exact hgap' e₀ h (m + k) hk

  have hK₀ : IsCompact ({g₀} : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) := isCompact_singleton
  have horth : ∀ k ∈ ({g₀} : Set (AdelicGL 3 (𝓞 ℚ) ℚ)), archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 := by
    intro k hk; rw [Set.mem_singleton_iff.1 hk]; exact hg₀
  obtain ⟨Cv, hCv_cont, CB, hCv⟩ := JointSliceLib.expansion_on_slice_first_vec_slab ρ nS D eS heS δS hδS q
    (fun μ h hμ => hcov μ (Or.inl h) hμ) hgap D le_rfl
    (fun r' d'' L m ρ' θ hθ => hE ℂ r' d'' L m ρ' θ hθ) N u h1 h8 r d d₂ w κf Mc A hw0 hκ0 hMc hA
    (fun g hg => (hsysg g hg).1)
    (fun g hg F hF => by
      obtain ⟨Fy, _, hFy, _⟩ := ((hsysg g hg).2.2 F hF).2
      exact ⟨Fy, hFy⟩)
    {g₀} hK₀ horth (2 * Z) (by linarith)

  obtain ⟨n9, J9, e9, δ9, hδ9, he9, hre9, H9⟩ :=
    exists_exponents_whittaker3_diag_joint_expansion_of_casimir_relations ω N₂ a₂ ha₂ N₃ a₃ ha₃ ρ
  have hu : InBlock ω a₂ a₃ N u := ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have HS : ∀ v : G3 → ℂ, InBlock ω a₂ a₃ N v → ∃ (c9 : Fin n9 → Fin J9 → ℝ → G3 → ℂ)
      (c9' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ), Spec ρ δ9 e9 v c9 c9' := by
    intro v hv
    obtain ⟨⟨c9, hc9, he1, c9', hc9', he2⟩, -⟩ := H9 N v hv.h1 hv.h2 hv.h3 hv.h4 hv.h5 hv.h6 hv.h7 hv.h8
    exact ⟨c9, c9', ⟨hc9, he1, hc9', he2⟩⟩
  clear H9
  have hclaim := claim_words hu hδ9 he9 hre9 HS
    (fun c9 c9' S => claim_base hδ hδ9 hinj hre he9 hre9 hC i j hlead hflat S)

  have HSl : ∀ l : Fin (r + 1), ∃ (cl : Fin n9 → Fin J9 → ℝ → G3 → ℂ)
      (cl' : Fin n9 → Fin J9 → Fin n9 → Fin J9 → G3 → ℂ), Spec ρ δ9 e9 (wordFn u (w l)) cl cl' :=
    fun l => HS _ (hu.word (w l))
  choose cl cl' hSl using HSl
  have hcl_claim : ∀ l, Claim e9 (e i) (j : ℕ) (cl l) (cl' l) := fun l => hclaim (w l) (cl l) (cl' l) (hSl l)

  have identV : ∀ z ∈ Set.Ioc (0 : ℝ) (2 * Z), ∀ l : Fin (r + 1),
      (∀ (iS : Fin nS) (jD : Fin D) (i9 : Fin n9) (j9 : Fin J9), eS iS = e9 i9 → (jD : ℕ) = (j9 : ℕ) →
        Cv iS jD z g₀ l = cl l i9 j9 z (g₀ * κf l)) ∧
      (∀ (iS : Fin nS) (jD : Fin D), (∀ (i9 : Fin n9) (j9 : Fin J9), ¬ (e9 i9 = eS iS ∧ (j9 : ℕ) = (jD : ℕ))) →
        Cv iS jD z g₀ l = 0) := by
    intro z hz l
    obtain ⟨b, hb, hbz, hzb⟩ := exists_band hz.1
    obtain ⟨C₂, hC₂⟩ := (hSl l).exp1 {g₀ * κf l} isCompact_singleton b hb
    have h1 : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖Wh (wordFn u (w l)) (tor y z * (g₀ * κf l)) -
          ∑ iS, ∑ jD, Cv iS jD z g₀ l * ((y : ℂ) ^ eS iS * ((Real.log y : ℝ) : ℂ) ^ (jD : ℕ))‖ ≤
          K * y ^ (ρ + δS) := by
      refine ⟨CB * z ^ (-(N : ℝ)), fun y hy hy1 => ?_⟩
      have hv := ((hCv g₀ rfl z hz).2 y ⟨hy, hy1⟩)
      refine le_trans ?_ hv
      have hcoord := norm_le_pi_norm ((fun l : Fin (r + 1) => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥)
        (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w l))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κf l)) -
        ∑ i : Fin nS, ∑ j : Fin D, ((y : ℂ) ^ eS i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • Cv i j z g₀) l
      refine le_trans (le_of_eq ?_) hcoord
      congr 1
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
      congr 1
      refine Finset.sum_congr rfl fun iS _ => Finset.sum_congr rfl fun jD _ => ?_
      ring
    have U := uniq2 eS heS e9 he9 (fun iS jD => Cv iS jD z g₀ l) (fun i9 j9 => cl l i9 j9 z (g₀ * κf l))
      (ρ + δS) (ρ + δ9) (fun y => Wh (wordFn u (w l)) (tor y z * (g₀ * κf l))) h1
      ⟨C₂, fun y hy hy1 => hC₂ _ rfl z hbz hzb y hy hy1⟩
    refine ⟨fun iS jD i9 j9 he' hj' => U.1 iS jD i9 j9 he' hj' ?_, fun iS jD hno => U.2.2 iS jD ?_ hno⟩
    · have := hreS iS; rw [lt_min_iff]; constructor <;> linarith
    · have := hreS iS; rw [lt_min_iff]; constructor <;> linarith

  have hL4 : ∀ iS : Fin nS, (eS iS).re < (e i).re → ∀ jD : Fin D, ∀ z ∈ Set.Ioc (0 : ℝ) (2 * Z),
      Cv iS jD z g₀ = 0 := by
    intro iS hiS jD z hz
    funext l
    by_cases hex : ∃ (i9 : Fin n9) (j9 : Fin J9), e9 i9 = eS iS ∧ (j9 : ℕ) = (jD : ℕ)
    · obtain ⟨i9, j9, he', hj'⟩ := hex
      rw [(identV z hz l).1 iS jD i9 j9 he'.symm hj'.symm]
      exact (hcl_claim l).1 i9 (by rw [he']; exact hiS) j9 _ z hz.1
    · push Not at hex
      exact (identV z hz l).2 iS jD fun i9 j9 h => hex i9 j9 h.1 h.2

  have hL5 : ∀ iS : Fin nS, eS iS = e i → ∀ jD : Fin D, (j : ℕ) ≤ (jD : ℕ) →
      ∃ C : ℝ, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖Cv iS jD z g₀‖ ≤ C * z ^ (ρ + δ9) := by
    intro iS hiS jD hjD
    have hsub : ∀ z ∈ Set.Ioc (0 : ℝ) 1, z ∈ Set.Ioc (0 : ℝ) (2 * Z) := fun z hz => ⟨hz.1, by linarith [hz.2]⟩
    have hcoord : ∀ l : Fin (r + 1), ∃ C : ℝ, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖Cv iS jD z g₀ l‖ ≤ C * z ^ (ρ + δ9) := by
      intro l
      by_cases hex : ∃ (i9 : Fin n9) (j9 : Fin J9), e9 i9 = eS iS ∧ (j9 : ℕ) = (jD : ℕ)
      · obtain ⟨i9, j9, he', hj'⟩ := hex
        obtain ⟨C, hC'⟩ := (hSl l).exp2 {g₀ * κf l} isCompact_singleton
        refine ⟨C, fun z hz => ?_⟩
        rw [(identV z (hsub z hz) l).1 iS jD i9 j9 he'.symm hj'.symm]
        have h0 : ∀ (i' : Fin n9) (j'' : Fin J9), cl' l i9 j9 i' j'' (g₀ * κf l) = 0 :=
          fun i' j'' => (hcl_claim l).2 i9 (he'.trans hiS) j9 (hj'.symm ▸ hjD) i' j'' _
        have := hC' _ rfl i9 j9 z hz.1 hz.2
        simpa only [h0, zero_mul, Finset.sum_const_zero, sub_zero] using this
      · push Not at hex
        refine ⟨0, fun z hz => ?_⟩
        rw [(identV z (hsub z hz) l).2 iS jD fun i9 j9 h => hex i9 j9 h.1 h.2]
        simp
    choose Cl hCl using hcoord
    refine ⟨∑ l, max (Cl l) 0, fun z hz => ?_⟩
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun l _ => le_max_right _ _)
      (Real.rpow_nonneg hz.1.le _))).2 fun l => ?_
    refine (hCl l z hz).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hz.1.le _)
    exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun l => max (Cl l) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ l))

  have ident0 : ∀ z ∈ Set.Ioc (0 : ℝ) (2 * Z),
      (∀ (iS : Fin nS) (jD : Fin D) (i'' : Fin n) (j'' : Fin J), eS iS = e i'' → (jD : ℕ) = (j'' : ℕ) →
        Cv iS jD z g₀ 0 = c i'' j'' z g₀) ∧
      (∀ (i'' : Fin n) (j'' : Fin J), (∀ (iS : Fin nS) (jD : Fin D), ¬ (eS iS = e i'' ∧ (jD : ℕ) = (j'' : ℕ))) →
        c i'' j'' z g₀ = 0) := by
    intro z hz
    obtain ⟨b, hb, hbz, hzb⟩ := exists_band hz.1
    obtain ⟨C₂, hC₂⟩ := hC {g₀} isCompact_singleton b hb
    have h1 : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖Wh u (tor y z * g₀) -
          ∑ iS, ∑ jD, Cv iS jD z g₀ 0 * ((y : ℂ) ^ eS iS * ((Real.log y : ℝ) : ℂ) ^ (jD : ℕ))‖ ≤
          K * y ^ (ρ + δS) := by
      refine ⟨CB * z ^ (-(N : ℝ)), fun y hy hy1 => ?_⟩
      have hv := ((hCv g₀ rfl z hz).2 y ⟨hy, hy1⟩)
      refine le_trans ?_ hv
      have hcoord := norm_le_pi_norm ((fun l : Fin (r + 1) => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥)
        (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w l))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κf l)) -
        ∑ i : Fin nS, ∑ j : Fin D, ((y : ℂ) ^ eS i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • Cv i j z g₀) 0
      refine le_trans (le_of_eq ?_) hcoord
      congr 1
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hw0, hκ0, mul_one,
        List.foldr_nil]
      congr 1
      refine Finset.sum_congr rfl fun iS _ => Finset.sum_congr rfl fun jD _ => ?_
      ring
    have U := uniq2 eS heS e hinj (fun iS jD => Cv iS jD z g₀ 0) (fun i'' j'' => c i'' j'' z g₀)
      (ρ + δS) (ρ + δ) (fun y => Wh u (tor y z * g₀)) h1
      ⟨C₂, fun y hy hy1 => hC₂ _ rfl z hbz hzb y hy hy1⟩
    refine ⟨fun iS jD i'' j'' he' hj' => U.1 iS jD i'' j'' he' hj' ?_, fun i'' j'' hno => U.2.1 i'' j'' ?_ hno⟩
    · have := hreS iS; rw [lt_min_iff]; constructor <;> linarith
    · have := hre i''; rw [lt_min_iff]; constructor <;> linarith

  have hcore : ∃ (σ B : ℝ) (V V' : ℝ → (Fin (r + 1) → ℂ)), ρ < σ ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt V (V' s) s ∧
        (s : ℂ) • V' s = (fun a => ∑ b, Mc' g₀ 0 a b • V s b) +
          ∑ k : Fin d', ((s : ℂ) ^ ((k : ℕ) + 1)) • (((Z : ℂ) ^ ((k : ℕ) + 1)) • A' g₀ k 0) (V s)) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖V s‖ ≤ B * s ^ σ) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, V s 0 = c i j' (Z * s) g₀) := by
    by_cases hmain : ∃ (iS : Fin nS) (jD : Fin D), eS iS = e i ∧ (jD : ℕ) = (j' : ℕ)
    swap
    ·
      push Not at hmain
      refine ⟨ρ + 1, 0, 0, 0, by linarith, fun s hs => ⟨hasDerivAt_const s 0, ?_⟩, fun s hs => by simp,
        fun s hs => ?_⟩
      · ext a; simp
      · have hz : Z * s ∈ Set.Ioc (0 : ℝ) (2 * Z) := mul_mem_slab hZ hs.1 (by linarith [hs.2])
        rw [(ident0 _ hz).2 i j' fun iS jD h => hmain iS jD h.1 h.2]
        rfl
    obtain ⟨i₀, jD, hi₀, hjD⟩ := hmain

    set Fw : ℝ → ℝ → (Fin (r + 1) → ℂ) := fun y z l => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥)
        (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w l))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κf l) with hFw
    obtain ⟨Fy, Fz, -, hFz⟩ := ((hsysg g₀ hg₀).2.2 Fw (fun _ _ _ => rfl)).2
    have hderiv := RegularSingular.hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le
      eS heS ρ δS hδS hreS hcl hgapF (Mc' g₀) (fun k a => ((Z : ℂ) ^ ((k : ℕ) + 1)) • A' g₀ k a)
      (fun y s => Fw y (Z * s)) (fun y s => (Z : ℝ) • Fz y (Z * s))
      (fun y hy s hs => by
        have hzs : 0 < Z * s := mul_pos hZ0 hs.1
        obtain ⟨hd, hsys⟩ := hFz y hy.1 (Z * s) hzs
        refine ⟨?_, ?_⟩
        · have := hd.scomp s ((hasDerivAt_id s).const_mul Z)
          simpa only [mul_one, Function.comp_def] using this
        · show (s : ℂ) • ((Z : ℝ) • Fz y (Z * s)) = _
          rw [← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul, mul_comm s Z, hsys]
          congr 1
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
          rw [ContinuousLinearMap.smul_apply, smul_smul, Complex.ofReal_mul, mul_pow]
          ring_nf)
      (fun iS jD s => Cv iS jD (Z * s) g₀)
      (fun iS jD => by
        refine (hCv_cont iS jD).comp ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn ?_
        intro s hs
        exact ⟨mul_mem_slab hZ hs.1 hs.2, rfl⟩)
      (fun s₀ hs₀ => by
        have hs00 : 0 < s₀ := hs₀.1
        refine ⟨|CB| * (Z * (s₀ / 2)) ^ (-(N : ℝ)), s₀ / 2, by linarith, fun s hs hss y hy => ?_⟩
        have hzs : Z * s ∈ Set.Ioc (0 : ℝ) (2 * Z) := mul_mem_slab hZ hs.1 hs.2
        have hv := (hCv g₀ rfl (Z * s) hzs).2 y hy
        refine hv.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy.1.le _)
        have hlow : Z * (s₀ / 2) ≤ Z * s := by
          rw [abs_lt] at hss
          exact mul_le_mul_of_nonneg_left (by linarith) hZ0.le
        have hpos : 0 < Z * (s₀ / 2) := mul_pos hZ0 (by linarith)
        calc CB * (Z * s) ^ (-(N : ℝ)) ≤ |CB| * (Z * s) ^ (-(N : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hzs.1.le _)
          _ ≤ |CB| * (Z * (s₀ / 2)) ^ (-(N : ℝ)) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos hlow (by simp)) (abs_nonneg _))

    set V : ℝ → (Fin (r + 1) → ℂ) := fun s => Cv i₀ jD (Z * s) g₀ with hV
    set V' : ℝ → (Fin (r + 1) → ℂ) := fun s => (s : ℂ)⁻¹ • (Matrix.mulVec (Mc' g₀ 0) (V s) +
      ∑ k : Fin d', ((s : ℂ) ^ ((k : ℕ) + 1)) • (((Z : ℂ) ^ ((k : ℕ) + 1)) • A' g₀ k 0) (V s)) with hV'

    have hcollapse : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
        (∑ a : Fin (d₂' + 1), ∑ i' : Fin nS, if eS i' + (a : ℕ) = eS i₀ then
          Matrix.mulVec (Mc' g₀ a) (Cv i' jD (Z * s) g₀) +
            ∑ k : Fin d', ((s : ℂ) ^ ((k : ℕ) + 1)) • (((Z : ℂ) ^ ((k : ℕ) + 1)) • A' g₀ k a) (Cv i' jD (Z * s) g₀)
          else 0) =
        Matrix.mulVec (Mc' g₀ 0) (V s) +
          ∑ k : Fin d', ((s : ℂ) ^ ((k : ℕ) + 1)) • (((Z : ℂ) ^ ((k : ℕ) + 1)) • A' g₀ k 0) (V s) := by
      intro s hs
      have hzs : Z * s ∈ Set.Ioc (0 : ℝ) (2 * Z) := mul_mem_slab hZ hs.1 (by linarith [hs.2])
      rw [Finset.sum_eq_single_of_mem (0 : Fin (d₂' + 1)) (Finset.mem_univ _)]
      · simp only [Fin.val_zero, Nat.cast_zero, add_zero, heS.eq_iff]
        rw [Finset.sum_ite_eq' Finset.univ i₀]
        simp only [Finset.mem_univ, if_true]
        rfl
      · intro a _ ha
        refine Finset.sum_eq_zero fun i' _ => ?_
        split_ifs with hcond
        · have hlt : (eS i').re < (e i).re := by
            have ha1 : (1 : ℕ) ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => ha (Fin.ext h))
            have h2 : (eS i').re + (a : ℕ) = (e i).re := by
              rw [← hi₀, ← hcond]; simp
            have h3 : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha1
            linarith
          rw [hL4 i' hlt jD (Z * s) hzs]
          simp
        · rfl

    obtain ⟨C₁, hC₁⟩ := hL5 i₀ hi₀ jD (by rw [hjD]; exact hjj')
    have hIc : IsCompact (Set.Icc Z⁻¹ (1 : ℝ)) := isCompact_Icc
    have hZi : 0 < Z⁻¹ := inv_pos.2 hZ0
    have hVcont : ContinuousOn V (Set.Icc Z⁻¹ 1) := by
      refine (hCv_cont i₀ jD).comp ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn ?_
      intro s hs
      exact ⟨mul_mem_slab hZ (hZi.trans_le hs.1) (show s ≤ 2 by linarith [hs.2]), rfl⟩
    obtain ⟨M, hM⟩ := hIc.exists_bound_of_continuousOn hVcont
    have hne : (Set.Icc Z⁻¹ (1 : ℝ)).Nonempty := ⟨1, ⟨inv_le_one_of_one_le₀ hZ, le_rfl⟩⟩
    have hrc : ContinuousOn (fun s : ℝ => s ^ (ρ + δ9)) (Set.Icc Z⁻¹ 1) :=
      continuousOn_id.rpow_const fun x hx => Or.inl (hZi.trans_le hx.1).ne'
    obtain ⟨s₁, hs₁, hmin⟩ := hIc.exists_isMinOn hne hrc
    have hs₁0 : 0 < s₁ := hZi.trans_le hs₁.1
    have hm₀ : 0 < s₁ ^ (ρ + δ9) := Real.rpow_pos_of_pos hs₁0 _
    have hMC0 : 0 ≤ max C₁ 0 * Z ^ (ρ + δ9) := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hZ0.le _)
    have hMM0 : 0 ≤ max M 0 / s₁ ^ (ρ + δ9) := div_nonneg (le_max_right _ _) hm₀.le
    refine ⟨ρ + δ9, max C₁ 0 * Z ^ (ρ + δ9) + max M 0 / s₁ ^ (ρ + δ9), V, V', by linarith,
      fun s hs => ⟨?_, ?_⟩, fun s hs => ?_, fun s hs => ?_⟩
    ·
      have h := hderiv i₀ jD s ⟨hs.1, by linarith [hs.2]⟩
      rw [hcollapse s hs] at h
      exact h
    · have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.1.ne'
      rw [hV', smul_smul, mul_inv_cancel₀ hs0, one_smul]
      rfl
    ·
      have hsσ : 0 ≤ s ^ (ρ + δ9) := Real.rpow_nonneg hs.1.le _
      rw [add_mul]
      rcases le_or_gt (Z * s) 1 with hzs | hzs
      · have h := hC₁ (Z * s) ⟨mul_pos hZ0 hs.1, hzs⟩
        rw [Real.mul_rpow hZ0.le hs.1.le] at h
        calc ‖V s‖ ≤ C₁ * (Z ^ (ρ + δ9) * s ^ (ρ + δ9)) := h
          _ ≤ max C₁ 0 * (Z ^ (ρ + δ9) * s ^ (ρ + δ9)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (Real.rpow_nonneg hZ0.le _) hsσ)
          _ = max C₁ 0 * Z ^ (ρ + δ9) * s ^ (ρ + δ9) := by ring
          _ ≤ max C₁ 0 * Z ^ (ρ + δ9) * s ^ (ρ + δ9) + max M 0 / s₁ ^ (ρ + δ9) * s ^ (ρ + δ9) :=
              le_add_of_nonneg_right (mul_nonneg hMM0 hsσ)
      · have hsI : s ∈ Set.Icc Z⁻¹ (1 : ℝ) :=
          ⟨by rw [inv_le_iff_one_le_mul₀ hZ0, mul_comm]; exact hzs.le, hs.2⟩
        have h := hM s hsI
        have hlow : s₁ ^ (ρ + δ9) ≤ s ^ (ρ + δ9) := hmin hsI
        calc ‖V s‖ ≤ max M 0 := h.trans (le_max_left _ _)
          _ = max M 0 / s₁ ^ (ρ + δ9) * s₁ ^ (ρ + δ9) := (div_mul_cancel₀ _ hm₀.ne').symm
          _ ≤ max M 0 / s₁ ^ (ρ + δ9) * s ^ (ρ + δ9) := mul_le_mul_of_nonneg_left hlow hMM0
          _ ≤ max C₁ 0 * Z ^ (ρ + δ9) * s ^ (ρ + δ9) + max M 0 / s₁ ^ (ρ + δ9) * s ^ (ρ + δ9) :=
              le_add_of_nonneg_left (mul_nonneg hMC0 hsσ)
    ·
      have hzs : Z * s ∈ Set.Ioc (0 : ℝ) (2 * Z) := mul_mem_slab hZ hs.1 (by linarith [hs.2])
      exact (ident0 _ hzs).1 i₀ jD i j' hi₀ hjD
  obtain ⟨σ, B, V, V', hρσ, hsysV, hflatV, hcoord⟩ := hcore
  refine ⟨r + 1, d', Mc' g₀ 0, fun k => ((Z : ℂ) ^ ((k : ℕ) + 1)) • A' g₀ k 0, q', σ, B, V, V', 0, hq', ?_, ?_,
    hsysV, hflatV, hcoord⟩
  · exact Polynomial.aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero (r + 1) d₂' (Mc' g₀) q'
      (hsysg g₀ hg₀).2.1
  · intro x hx; exact lt_of_le_of_lt (hroots x hx) hρσ

end S_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations (solution)
