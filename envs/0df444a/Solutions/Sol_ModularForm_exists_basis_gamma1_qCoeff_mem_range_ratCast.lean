-- Prove2me | solution 1 for ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3f576c12-c3bd-5dd4-b0e0-841b8dce8d63

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp
import Theorems.Thm_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GammaOneRationalStructureMF

variable (N : ℕ)

def zetaN : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

theorem kN_eq : kN N = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} :=
  rfl

section Cyclo

variable [NeZero N]

theorem isPrimitiveRoot_zetaN : IsPrimitiveRoot (zetaN N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

scoped instance instIsCyclotomic : IsCyclotomicExtension {N} ℚ (kN N) := by
  have hζ := isPrimitiveRoot_zetaN N
  change IsCyclotomicExtension {N} ℚ (IntermediateField.adjoin ℚ {zetaN N}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos N)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

scoped instance instIsGalois : IsGalois ℚ (kN N) := IsCyclotomicExtension.isGalois {N} ℚ (kN N)

scoped instance instFiniteDimensional : FiniteDimensional ℚ (kN N) :=
  IsCyclotomicExtension.finiteDimensional {N} ℚ (kN N)

omit [NeZero N] in

theorem coe_algebraMap_rat (r : ℚ) : ((algebraMap ℚ (kN N) r : kN N) : ℂ) = (r : ℂ) := by
  rw [eq_ratCast (algebraMap ℚ (kN N)) r, SubfieldClass.coe_ratCast]

theorem exists_rat_sum_aut (x : kN N) :
    ∃ r : ℚ, (∑ σ : (kN N) ≃ₐ[ℚ] (kN N), ((σ x : kN N) : ℂ)) = (r : ℂ) := by
  refine ⟨Algebra.trace ℚ (kN N) x, ?_⟩
  have h := trace_eq_sum_automorphisms (K := ℚ) (L := kN N) x
  rw [← AddSubmonoidClass.coe_finsetSum, ← h, coe_algebraMap_rat]

end Cyclo

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {N} {k : ℤ}

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

def qCoeffLin (N : ℕ) (k : ℤ) (m : ℕ) : ModularForm (Γ₁ℝ N) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff f m
  map_add' f g := by
    change (qExpansion 1 (⇑(f + g))).coeff m = (qExpansion 1 ⇑f).coeff m + (qExpansion 1 ⇑g).coeff m
    rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g, map_add]
  map_smul' a f := by
    change (qExpansion 1 (⇑(a • f))).coeff m = a * (qExpansion 1 ⇑f).coeff m
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) a f,
      map_smul, smul_eq_mul]

@[scoped simp] theorem qCoeffLin_apply (m : ℕ) (f : ModularForm (Γ₁ℝ N) k) :
    qCoeffLin N k m f = ModularFormClass.qCoeff f m := rfl

theorem eq_of_qCoeff_eq [NeZero N] (f g : ModularForm (Γ₁ℝ N) k)
    (h : ∀ m : ℕ, ModularFormClass.qCoeff f m = ModularFormClass.qCoeff g m) : f = g := by
  have hsub : ∀ m, ModularFormClass.qCoeff (⇑(f - g)) m = 0 := by
    intro m
    have := (qCoeffLin N k m).map_sub f g
    simp only [qCoeffLin_apply] at this
    rw [this, h m, sub_self]
  have hq : qExpansion 1 (⇑(f - g)) = 0 := by
    ext m
    simpa [ModularFormClass.qCoeff] using hsub m
  have hzero : (⇑(f - g) : ℍ → ℂ) = 0 := by
    have hper := SlashInvariantFormClass.periodic_comp_ofComplex (f - g) (one_mem_strictPeriods N)
    have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑(f - g)) := (f - g).holo'
    have hbdd : IsBoundedAtImInfty (⇑(f - g)) := ModularFormClass.bdd_at_infty (f - g)
    exact (qExpansion_eq_zero_iff one_pos hper hhol hbdd).1 hq
  have : f - g = 0 := DFunLike.ext _ _ fun τ => by simpa using congrFun hzero τ
  exact sub_eq_zero.1 this

section Trace

variable (N) [NeZero N] (k)

def ratForms : Set (ModularForm (Γ₁ℝ N) k) :=
  {g | ∀ m : ℕ, ModularFormClass.qCoeff g m ∈ Set.range ((↑) : ℚ → ℂ)}

variable {N k}

theorem mem_span_ratForms (f : ModularForm (Γ₁ℝ N) k) (c : ℕ → kN N)
    (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    f ∈ Submodule.span ℂ (ratForms N k) := by
  classical

  have hpart : ∀ σ : (kN N) ≃ₐ[ℚ] (kN N), ∃ f' : ModularForm (Γ₁ℝ N) k,
      ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := fun σ =>
    ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply N k (kN N) (kN_eq N) σ f c hf
  choose fσ hfσ using hpart

  have hone : fσ 1 = f := eq_of_qCoeff_eq _ _ fun m => by rw [hfσ 1 m, hf m]; rfl

  let T : kN N → ModularForm (Γ₁ℝ N) k := fun x => ∑ σ, ((σ x : kN N) : ℂ) • fσ σ
  have hT : ∀ x, T x ∈ ratForms N k := by
    intro x m
    have hlin : ModularFormClass.qCoeff (⇑(T x)) m = ∑ σ : (kN N) ≃ₐ[ℚ] (kN N),
        ((σ x : kN N) : ℂ) * (σ (c m) : ℂ) := by
      have := map_sum (qCoeffLin N k m) (fun σ => ((σ x : kN N) : ℂ) • fσ σ) Finset.univ
      simp only [qCoeffLin_apply, map_smul, smul_eq_mul] at this
      rw [show T x = ∑ σ, ((σ x : kN N) : ℂ) • fσ σ from rfl, this]
      exact Finset.sum_congr rfl fun σ _ => by rw [hfσ σ m]
    obtain ⟨r, hr⟩ := exists_rat_sum_aut N (x * c m)
    refine ⟨r, ?_⟩
    rw [hlin, ← hr]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, MulMemClass.coe_mul]

  have hded : LinearIndependent ℂ (fun σ : (kN N) ≃ₐ[ℚ] (kN N) => fun y : kN N => ((σ y : kN N) : ℂ)) := by
    have h0 := linearIndependent_monoidHom (kN N) ℂ
    let ι : ((kN N) ≃ₐ[ℚ] (kN N)) → (kN N →* ℂ) := fun σ =>
      ((algebraMap (kN N) ℂ : kN N →+* ℂ) : kN N →* ℂ).comp (σ : (kN N) ≃ₐ[ℚ] (kN N)).toRingEquiv.toMonoidHom
    have hι : Function.Injective ι := by
      intro σ τ hστ
      apply AlgEquiv.ext
      intro y
      have := DFunLike.congr_fun hστ y
      exact Subtype.ext this
    have h1 := h0.comp ι hι
    convert h1 using 1
    rfl
    rfl

  set n : ℕ := Module.finrank ℚ (kN N) with hn
  let bK := Module.finBasis ℚ (kN N)
  have hcard : Fintype.card ((kN N) ≃ₐ[ℚ] (kN N)) = n := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank ℚ (kN N)
  let e : ((kN N) ≃ₐ[ℚ] (kN N)) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => (((e.symm i) (bK j) : kN N) : ℂ)

  have hinj : Function.Injective M.vecMul := by
    intro a a' haa
    have hzero : ∀ a₀ : Fin n → ℂ, M.vecMul a₀ = 0 → a₀ = 0 := by
      intro a₀ ha₀

      have hvan : ∀ y : kN N, ∑ i, a₀ i * (((e.symm i) y : kN N) : ℂ) = 0 := by
        intro y
        have hy := bK.sum_repr y
        have step : ∀ i, (((e.symm i) y : kN N) : ℂ) = ∑ j, ((bK.repr y j : ℚ) : ℂ) *
            (((e.symm i) (bK j) : kN N) : ℂ) := by
          intro i
          conv_lhs => rw [← hy, map_sum, AddSubmonoidClass.coe_finsetSum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, MulMemClass.coe_mul, coe_algebraMap_rat]
        have hj : ∀ j, ∑ i, a₀ i * (((e.symm i) (bK j) : kN N) : ℂ) = 0 := by
          intro j
          have := congrFun ha₀ j
          simpa [Matrix.vecMul, dotProduct, M] using this
        calc ∑ i, a₀ i * (((e.symm i) y : kN N) : ℂ)
            = ∑ i, a₀ i * ∑ j, ((bK.repr y j : ℚ) : ℂ) * (((e.symm i) (bK j) : kN N) : ℂ) := by
              exact Finset.sum_congr rfl fun i _ => by rw [step i]
          _ = ∑ j, ((bK.repr y j : ℚ) : ℂ) * ∑ i, a₀ i * (((e.symm i) (bK j) : kN N) : ℂ) := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
          _ = 0 := by simp [hj]

      have hfam : ∑ σ : (kN N) ≃ₐ[ℚ] (kN N), a₀ (e σ) •
          (fun y : kN N => ((σ y : kN N) : ℂ)) = 0 := by
        funext y
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hvan y]
        exact Fintype.sum_equiv e _ _ fun σ => by simp
      have := linearIndependent_iff'.1 hded Finset.univ (fun σ => a₀ (e σ)) hfam
      funext i
      have hi := this (e.symm i) (Finset.mem_univ _)
      simpa using hi
    have hlinmap : M.vecMul (a - a') = 0 := by
      have h' : M.vecMul a = M.vecMul a' := haa
      rw [show M.vecMul (a - a') = M.vecMul a - M.vecMul a' from Matrix.sub_vecMul M a a', h', sub_self]
    exact sub_eq_zero.1 (hzero _ hlinmap)
  have hunit : IsUnit M := Matrix.vecMul_injective_iff_isUnit.1 hinj
  obtain ⟨d, hd⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hunit (Pi.single (e 1) 1)

  have hδ : ∀ σ : (kN N) ≃ₐ[ℚ] (kN N), ∑ j, (((σ (bK j) : kN N) : ℂ)) * d j =
      if σ = 1 then 1 else 0 := by
    intro σ
    have := congrFun hd (e σ)
    simp only [Matrix.mulVec, dotProduct, M, Equiv.symm_apply_apply] at this
    rw [this, Pi.single_apply]
    simp [e.injective.eq_iff]

  have hcomb : (∑ j, d j • T (bK j)) = f := by
    have : (∑ j, d j • T (bK j)) = ∑ σ, (∑ j, ((σ (bK j) : kN N) : ℂ) * d j) • fσ σ := by
      simp only [T, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    rw [this]
    have hσ : ∀ σ : (kN N) ≃ₐ[ℚ] (kN N),
        (∑ j, ((σ (bK j) : kN N) : ℂ) * d j) • fσ σ = if σ = 1 then fσ σ else 0 := fun σ => by
      rw [hδ σ]; split_ifs <;> simp
    rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_ite_eq']
    simp [hone]
  rw [← hcomb]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hT _))

end Trace

theorem main (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (ModularForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ) := by
  classical

  obtain ⟨n₀, b₀, hb₀⟩ := ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp N k
  haveI : FiniteDimensional ℂ (ModularForm (Γ₁ℝ N) k) := b₀.finiteDimensional_of_finite

  have hspan : Submodule.span ℂ (ratForms N k) = ⊤ := by
    rw [eq_top_iff, ← b₀.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    let c : ℕ → kN N := fun m => ⟨ModularFormClass.qCoeff (b₀ i) m, hb₀ i m⟩
    exact mem_span_ratForms (b₀ i) c fun m => rfl

  obtain ⟨t, ht_sub, ht_span, ht_ind⟩ := exists_linearIndependent ℂ (ratForms N k)
  have ht_fin : t.Finite := LinearIndependent.set_finite_of_isNoetherian ht_ind
  letI : Fintype t := ht_fin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → ModularForm (Γ₁ℝ N) k)) := by
    rw [Subtype.range_coe, ht_span, hspan]
  let B : Module.Basis t ℂ (ModularForm (Γ₁ℝ N) k) := Module.Basis.mk ht_ind htop
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨Fintype.card t, B.reindex e, fun i m => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact ht_sub (e.symm i).2 m

end GammaOneRationalStructureMF
p2m_reactivate "P2MW.S_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.GammaOneRationalStructureMF"

end
p2m_reactivate "P2MW.S_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.GammaOneRationalStructureMF"

theorem solution (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ) :=
  GammaOneRationalStructureMF.main N k

end S_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
end P2MW
export P2MW.S_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast (solution)
