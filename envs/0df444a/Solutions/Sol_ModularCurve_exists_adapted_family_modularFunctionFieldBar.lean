-- Prove2me | solution 1 for ModularCurve.exists_adapted_family_modularFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9058c194-6187-5a9b-9bef-fdf9e3844591

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_ord_cuspInftyBar
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_cuspInftyBar
import Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_adapted_family_modularFunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_adapted_family_modularFunctionFieldBar.ModularCurve AlgebraicCurve P2MW.S_ModularCurve_exists_adapted_family_modularFunctionFieldBar.AlgebraicCurve"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.smul_single Place Place.ord_one Divisor riemannRochSpace mem_riemannRochSpace_iff LSpace ConstantsAreBase"
namespace SemilinearAut
p2m_export "AlgebraicCurve.SemilinearAut" "smul_def ord_smul smul_single divisor_smul_apply"
p2m_open "AlgebraicCurve.SemilinearAut AlgebraicCurve"

theorem smul_mem_riemannRochSpace {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) {D : Divisor K F} {f : F} (hf : f ∈ riemannRochSpace D) :
    g • f ∈ riemannRochSpace (g • D) := by
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro w
  rcases hf (g⁻¹ • w) with h0 | hle
  · left; rw [h0, smul_zero]
  · right
    rw [divisor_smul_apply]
    have hw : (g • (g⁻¹ • w)).ord (g • f) = (g⁻¹ • w).ord f := ord_smul g (g⁻¹ • w) f
    rw [smul_inv_smul] at hw
    rw [hw]; exact hle

end AlgebraicCurve.SemilinearAut

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois coe_arithmeticGalois_smul modularFunctionFieldBar modularFunctionFieldFull coeffMap_coeff algebraMap_laurentSeries_eq_single cuspInftyBar ord_cuspInftyBar arithmeticGalois_smul_cuspInftyBar constantsAreBase_modularFunctionFieldBar"
namespace AdaptedFamilyAux
p2m_open "ModularCurve"

variable (N : ℕ) [NeZero N]

abbrev W (k : ℕ) : Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  riemannRochSpace ((k : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ))

theorem D_eq (k : ℕ) :
    ((k : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      = Finsupp.single (cuspInftyBar N) (k : ℤ) := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem D_apply_self (k : ℕ) :
    ((k : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) (cuspInftyBar N) = (k : ℤ) := by
  rw [D_eq, Finsupp.single_eq_same]

theorem D_apply_ne (k : ℕ) {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v ≠ cuspInftyBar N) :
    ((k : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) v = 0 := by
  rw [D_eq]
  first
    | exact Finsupp.single_eq_of_ne hv
    | exact Finsupp.single_eq_of_ne (Ne.symm hv)

def qcoeff (n : ℤ) : modularFunctionFieldBar N →ₗ[AlgebraicClosure ℚ] AlgebraicClosure ℚ where
  toFun f := (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n
  map_add' f g := by
    show ((f + g : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = _
    rw [IntermediateField.coe_add]; rfl
  map_smul' a f := by
    show ((a • f : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = _
    rw [IntermediateField.coe_smul, RingHom.id_apply, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
      HahnSeries.coeff_single_zero_mul, smul_eq_mul]

theorem qcoeff_apply (n : ℤ) (f : modularFunctionFieldBar N) :
    qcoeff N n f = (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n := rfl

theorem qcoeff_one (n : ℤ) : qcoeff N n (1 : modularFunctionFieldBar N) = if n = 0 then 1 else 0 := by
  rw [qcoeff_apply, OneMemClass.coe_one, HahnSeries.coeff_one]
  split_ifs <;> rfl

theorem eq_zero_of_forall_qcoeff_eq_zero (f : modularFunctionFieldBar N)
    (h : ∀ n : ℤ, qcoeff N n f = 0) : f = 0 := by
  have : (f : LaurentSeries (AlgebraicClosure ℚ)) = 0 := HahnSeries.ext (funext fun n => h n)
  exact_mod_cast this

theorem qcoeff_galois_smul (n : ℤ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f : modularFunctionFieldBar N) :
    qcoeff N n (arithmeticGalois (modularFunctionFieldFull N) σ • f) = σ (qcoeff N n f) := by
  rw [qcoeff_apply, qcoeff_apply, coe_arithmeticGalois_smul, coeffMap_coeff]
  rfl

theorem W_mono {j k : ℕ} (h : j ≤ k) : W N j ≤ W N k := by
  intro f hf v
  refine (hf v).trans (WithZero.exp_le_exp.mpr ?_)
  by_cases hv : v = cuspInftyBar N
  · rw [hv, D_apply_self, D_apply_self]; exact_mod_cast h
  · rw [D_apply_ne N j hv, D_apply_ne N k hv]

theorem one_mem_W (k : ℕ) : (1 : modularFunctionFieldBar N) ∈ W N k := by
  rw [mem_riemannRochSpace_iff]
  intro v; right
  rw [Place.ord_one]
  by_cases hv : v = cuspInftyBar N
  · rw [hv, D_apply_self]; omega
  · rw [D_apply_ne N k hv]; omega

theorem qcoeff_eq_zero_of_mem_W {k : ℕ} {f : modularFunctionFieldBar N} (hf : f ∈ W N k)
    {n : ℤ} (hn : n < -(k : ℤ)) : qcoeff N n f = 0 := by
  rw [mem_riemannRochSpace_iff] at hf
  rcases hf (cuspInftyBar N) with h0 | hle
  · rw [h0, map_zero]
  · rw [D_apply_self, ord_cuspInftyBar] at hle
    rw [qcoeff_apply]
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hn hle)

theorem mem_W_of_qcoeff_eq_zero {k : ℕ} {f : modularFunctionFieldBar N} (hf : f ∈ W N (k + 1))
    (h0 : qcoeff N (-((k : ℤ) + 1)) f = 0) : f ∈ W N k := by
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  by_cases hv : v = cuspInftyBar N
  · subst hv
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    rcases hf (cuspInftyBar N) with h0' | hle
    · exact Or.inl h0'
    right
    rw [D_apply_self] at hle ⊢
    rw [ord_cuspInftyBar] at hle ⊢
    have hne : (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
      intro h; apply hf0; exact_mod_cast h
    have hord : (f : LaurentSeries (AlgebraicClosure ℚ)).order ≠ -((k : ℤ) + 1) := by
      intro heq
      apply hne
      rw [← HahnSeries.coeff_order_eq_zero, heq]
      exact h0
    push_cast at hle
    omega
  · rcases hf v with h0' | hle
    · exact Or.inl h0'
    · right; rw [D_apply_ne N (k+1) hv] at hle; rw [D_apply_ne N k hv]; exact hle

theorem galois_smul_mem_W {k : ℕ} {f : modularFunctionFieldBar N} (hf : f ∈ W N k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull N) σ • f ∈ W N k := by
  have h := SemilinearAut.smul_mem_riemannRochSpace (arithmeticGalois (modularFunctionFieldFull N) σ) hf
  have hD : arithmeticGalois (modularFunctionFieldFull N) σ •
        ((k : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      = (k : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ) := by
    rw [D_eq, SemilinearAut.smul_single, arithmeticGalois_smul_cuspInftyBar]
  rw [hD] at h
  exact h

theorem qcoeff_neg_ne_zero_of_mem_W_of_not_mem {k : ℕ} {f : modularFunctionFieldBar N}
    (hf : f ∈ W N (k + 1)) (hf' : f ∉ W N k) : qcoeff N (-((k : ℤ) + 1)) f ≠ 0 :=
  fun h => hf' (mem_W_of_qcoeff_eq_zero N hf h)

theorem linearIndependent_of_dual_delta {R M ι : Type*} [Field R] [AddCommGroup M] [Module R M]
    [DecidableEq ι] (g : ι → M) (c : ι → M →ₗ[R] R)
    (h : ∀ i j, c j (g i) = if i = j then 1 else 0) :
    LinearIndependent R g := by
  rw [linearIndependent_iff]
  intro l hl
  ext j
  have key : c j (Finsupp.linearCombination R g l) = l j := by
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finsupp.sum_ite_eq']
    split_ifs with hj
    · rfl
    · exact (not_not.mp (mt Finsupp.mem_support_iff.mpr hj)).symm
  rw [hl, map_zero] at key
  simpa using key.symm

theorem eq_of_dual_delta_of_mem_span {R M ι : Type*} [Field R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (g : ι → M) (c : ι → M →ₗ[R] R)
    (h : ∀ i j, c j (g i) = if i = j then 1 else 0)
    {x : M} (hx : x ∈ Submodule.span R (Set.range g)) (i : ι)
    (hxi : ∀ j, c j x = if i = j then 1 else 0) : x = g i := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  have ha : ∀ j, a j = if i = j then 1 else 0 := by
    intro j
    have := hxi j
    simp only [map_sum, map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  simp only [ha, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem W_zero : W N 0 = Submodule.span (AlgebraicClosure ℚ) {(1 : modularFunctionFieldBar N)} := by
  have h : LSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      = LinearMap.range (Algebra.linearMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    ModularCurve.constantsAreBase_modularFunctionFieldBar N
  have h0 : ((0 : ℕ) : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ) = 0 := by simp
  show riemannRochSpace _ = _
  rw [h0]
  change LSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = _
  rw [h]
  ext x
  simp only [LinearMap.mem_range, Algebra.linearMap_apply, Submodule.mem_span_singleton,
    Algebra.algebraMap_eq_smul_one]

structure Stage (k : ℕ) (T : Finset ℕ) (g : ℕ → modularFunctionFieldBar N) : Prop where
  zero_mem : 0 ∈ T
  g_zero : g 0 = 1
  le_of_mem : ∀ o ∈ T, o ≤ k
  mem_W : ∀ o ∈ T, g o ∈ W N o
  delta : ∀ o ∈ T, ∀ o' ∈ T, qcoeff N (-(o' : ℤ)) (g o) = if o = o' then 1 else 0
  span_eq : ∀ j ≤ k,
    Submodule.span (AlgebraicClosure ℚ) (g '' (↑(T.filter (· ≤ j)) : Set ℕ)) = W N j

theorem stage_zero : Stage N 0 {0} (fun _ => 1) where
  zero_mem := Finset.mem_singleton_self 0
  g_zero := rfl
  le_of_mem o ho := by rw [Finset.mem_singleton] at ho; exact ho.le
  mem_W o _ := one_mem_W N o
  delta o ho o' ho' := by
    rw [Finset.mem_singleton] at ho ho'
    subst ho; subst ho'
    show qcoeff N (-((0 : ℕ) : ℤ)) 1 = _
    rw [qcoeff_one]; simp
  span_eq j hj := by
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    rw [W_zero]
    congr 1
    ext x
    simp

theorem stage_succ (k : ℕ) (T : Finset ℕ) (g : ℕ → modularFunctionFieldBar N)
    (hS : Stage N k T g) :
    ∃ (T' : Finset ℕ) (g' : ℕ → modularFunctionFieldBar N), Stage N (k + 1) T' g' := by
  have hTk : T.filter (· ≤ k) = T := Finset.filter_true_of_mem fun o ho => hS.le_of_mem o ho
  have hTk1 : T.filter (· ≤ k + 1) = T :=
    Finset.filter_true_of_mem fun o ho => (hS.le_of_mem o ho).trans k.le_succ
  have hWk : Submodule.span (AlgebraicClosure ℚ) (g '' (↑T : Set ℕ)) = W N k := by
    simpa [hTk] using hS.span_eq k le_rfl
  by_cases hW : W N (k + 1) ≤ W N k
  ·
    refine ⟨T, g, ⟨hS.zero_mem, hS.g_zero, fun o ho => (hS.le_of_mem o ho).trans k.le_succ,
      hS.mem_W, hS.delta, fun j hj => ?_⟩⟩
    rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
    · exact hS.span_eq j (Nat.lt_succ_iff.mp hj')
    · obtain rfl : j = k + 1 := le_antisymm hj hj'
      rw [hTk1, hWk]
      exact le_antisymm (W_mono N k.le_succ) hW
  ·
    obtain ⟨x, hx1, hx0⟩ := SetLike.not_le_iff_exists.mp hW
    set c : AlgebraicClosure ℚ := qcoeff N (-((k : ℤ) + 1)) x with hc_def
    have hc : c ≠ 0 := qcoeff_neg_ne_zero_of_mem_W_of_not_mem N hx1 hx0
    set x₁ : modularFunctionFieldBar N := c⁻¹ • x with hx₁_def
    have hx₁W : x₁ ∈ W N (k + 1) := Submodule.smul_mem _ _ hx1
    have hx₁c : qcoeff N (-((k : ℤ) + 1)) x₁ = 1 := by
      rw [hx₁_def, map_smul, smul_eq_mul, ← hc_def, inv_mul_cancel₀ hc]
    have hcast : (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 := by push_cast; ring
    set gnew : modularFunctionFieldBar N :=
      x₁ - ∑ o ∈ T, qcoeff N (-(o : ℤ)) x₁ • g o with hgnew_def
    have hk1 : k + 1 ∉ T := fun h => Nat.not_succ_le_self k (hS.le_of_mem _ h)

    have hold : ∀ o ∈ T, qcoeff N (-(((k + 1 : ℕ)) : ℤ)) (g o) = 0 := by
      intro o ho
      refine qcoeff_eq_zero_of_mem_W N (hS.mem_W o ho) ?_
      have := hS.le_of_mem o ho
      omega
    have hsumW : (∑ o ∈ T, qcoeff N (-(o : ℤ)) x₁ • g o) ∈ W N k :=
      Submodule.sum_mem _ fun o ho =>
        Submodule.smul_mem _ _ (W_mono N (hS.le_of_mem o ho) (hS.mem_W o ho))
    have hgnewW : gnew ∈ W N (k + 1) :=
      Submodule.sub_mem _ hx₁W (W_mono N k.le_succ hsumW)

    have hgnew_old : ∀ o' ∈ T, qcoeff N (-(o' : ℤ)) gnew = 0 := by
      intro o' ho'
      rw [hgnew_def, map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [Finset.sum_congr rfl fun o ho => by rw [hS.delta o ho o' ho']]
      simp [Finset.sum_ite_eq', ho']
    have hgnew_new : qcoeff N (-(((k + 1 : ℕ)) : ℤ)) gnew = 1 := by
      rw [hgnew_def, map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [Finset.sum_eq_zero fun o ho => by rw [hold o ho, mul_zero], sub_zero, hcast, hx₁c]
    let g' : ℕ → modularFunctionFieldBar N := fun o => if o = k + 1 then gnew else g o
    have hg'old : ∀ o ∈ T, g' o = g o := fun o ho => if_neg fun h : o = k + 1 => hk1 (h ▸ ho)
    have hg'new : g' (k + 1) = gnew := if_pos rfl
    refine ⟨insert (k + 1) T, g', ⟨Finset.mem_insert_of_mem hS.zero_mem, ?_, ?_, ?_, ?_, ?_⟩⟩
    ·
      rw [hg'old 0 hS.zero_mem, hS.g_zero]
    ·
      intro o ho
      rcases Finset.mem_insert.mp ho with rfl | ho
      · exact le_rfl
      · exact (hS.le_of_mem o ho).trans k.le_succ
    ·
      intro o ho
      rcases Finset.mem_insert.mp ho with rfl | ho
      · rw [hg'new]; exact hgnewW
      · rw [hg'old o ho]; exact hS.mem_W o ho
    ·
      intro o ho o' ho'
      rcases Finset.mem_insert.mp ho with rfl | ho
      · rw [hg'new]
        rcases Finset.mem_insert.mp ho' with rfl | ho'
        · rw [hgnew_new, if_pos rfl]
        · rw [hgnew_old o' ho', if_neg fun h : k + 1 = o' => hk1 (h ▸ ho')]
      · rw [hg'old o ho]
        rcases Finset.mem_insert.mp ho' with rfl | ho'
        · rw [hold o ho, if_neg fun h : o = k + 1 => hk1 (h ▸ ho)]
        · exact hS.delta o ho o' ho'
    ·
      intro j hj
      rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · have hj'' : j ≤ k := Nat.lt_succ_iff.mp hj'
        rw [Finset.filter_insert, if_neg (not_le.mpr hj'), ← hS.span_eq j hj'']
        congr 1
        refine Set.image_congr fun o ho => hg'old o ?_
        exact (Finset.mem_filter.mp ho).1
      · obtain rfl : j = k + 1 := le_antisymm hj hj'
        rw [Finset.filter_insert, if_pos le_rfl, hTk1, Finset.coe_insert, Set.image_insert_eq,
          hg'new, Set.image_congr fun o ho => hg'old o ho, Submodule.span_insert, hWk]
        apply le_antisymm
        · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hgnewW) (W_mono N k.le_succ)
        · intro y hy
          set a : AlgebraicClosure ℚ := qcoeff N (-((k : ℤ) + 1)) y with ha_def
          have hrest : y - a • x₁ ∈ W N k := by
            refine mem_W_of_qcoeff_eq_zero N (Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hx₁W)) ?_
            rw [map_sub, map_smul, smul_eq_mul, hx₁c, mul_one, ← ha_def, sub_self]
          have hx₁eq : x₁ = gnew + ∑ o ∈ T, qcoeff N (-(o : ℤ)) x₁ • g o := by
            rw [hgnew_def, sub_add_cancel]
          rw [(sub_add_cancel y (a • x₁)).symm]
          refine Submodule.add_mem _ (Submodule.mem_sup_right hrest) (Submodule.smul_mem _ a ?_)
          rw [hx₁eq]
          exact Submodule.add_mem _
            (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
            (Submodule.mem_sup_right hsumW)

theorem exists_stage (k : ℕ) :
    ∃ (T : Finset ℕ) (g : ℕ → modularFunctionFieldBar N), Stage N k T g := by
  induction k with
  | zero => exact ⟨{0}, fun _ => 1, stage_zero N⟩
  | succ k ih =>
    obtain ⟨T, g, hS⟩ := ih
    exact stage_succ N k T g hS

theorem Stage.galois_smul_eq {k : ℕ} {T : Finset ℕ} {g : ℕ → modularFunctionFieldBar N}
    (hS : Stage N k T g) (o : ℕ) (ho : o ∈ T)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull N) σ • g o = g o := by
  have hTk : T.filter (· ≤ k) = T := Finset.filter_true_of_mem fun o ho => hS.le_of_mem o ho
  have hWk : Submodule.span (AlgebraicClosure ℚ) (g '' (↑T : Set ℕ)) = W N k := by
    simpa [hTk] using hS.span_eq k le_rfl
  let G : ↥T → modularFunctionFieldBar N := fun p => g p
  let C : ↥T → modularFunctionFieldBar N →ₗ[AlgebraicClosure ℚ] AlgebraicClosure ℚ :=
    fun p => qcoeff N (-((p : ℕ) : ℤ))
  have hδ : ∀ p p' : ↥T, C p' (G p) = if p = p' then 1 else 0 := by
    intro p p'
    show qcoeff N (-((p' : ℕ) : ℤ)) (g p) = _
    rw [hS.delta p p.2 p' p'.2]
    by_cases h : p = p'
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg fun h' => h (Subtype.ext h')]
  have hmem : arithmeticGalois (modularFunctionFieldFull N) σ • g o
      ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range G) := by
    have : Set.range G = g '' (↑T : Set ℕ) := by
      ext y; constructor
      · rintro ⟨p, rfl⟩; exact ⟨p, p.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩; exact ⟨⟨q, hq⟩, rfl⟩
    rw [this, hWk]
    exact galois_smul_mem_W N (W_mono N (hS.le_of_mem o ho) (hS.mem_W o ho)) σ
  have := eq_of_dual_delta_of_mem_span G C hδ hmem ⟨o, ho⟩ fun p' => by
    show qcoeff N (-((p' : ℕ) : ℤ)) _ = _
    rw [qcoeff_galois_smul, hS.delta o ho p' p'.2]
    by_cases h : (⟨o, ho⟩ : ↥T) = p'
    · rw [if_pos h, if_pos (congrArg Subtype.val h), map_one]
    · rw [if_neg h, if_neg fun h' => h (Subtype.ext h'), map_zero]
  exact this

theorem main (m : ℕ) :
    ∃ (n : ℕ) (f : Fin (n + 1) → modularFunctionFieldBar N) (o : Fin (n + 1) → ℕ),
      f 0 = 1 ∧ (∀ i, f i ≠ 0) ∧
      (∀ (i : Fin (n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        arithmeticGalois (modularFunctionFieldFull N) σ • f i = f i) ∧
      (∀ k ≤ m, LinearIndependent (AlgebraicClosure ℚ)
            (fun i : {i : Fin (n + 1) // o i ≤ k} => f i) ∧
          Submodule.span (AlgebraicClosure ℚ)
              (Set.range (fun i : {i : Fin (n + 1) // o i ≤ k} => f i))
            = riemannRochSpace ((k : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ))) := by
  obtain ⟨T, g, hS⟩ := exists_stage N m
  have hTne : T.Nonempty := ⟨0, hS.zero_mem⟩
  obtain ⟨n, hn⟩ : ∃ n, T.card = n + 1 := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hTne).ne'
  let e : Fin (n + 1) ↪o ℕ := T.orderEmbOfFin hn
  have he_mem : ∀ i, e i ∈ T := fun i => Finset.orderEmbOfFin_mem T hn i
  have he_range : Set.range e = ↑T := Finset.range_orderEmbOfFin T hn
  have he0 : e 0 = 0 := by
    have h1 := Finset.orderEmbOfFin_zero hn (Nat.succ_pos n)
    have h2 : (0 : Fin (n + 1)) = ⟨0, Nat.succ_pos n⟩ := rfl
    rw [h2, h1]
    exact le_antisymm (Finset.min'_le T 0 hS.zero_mem) (Nat.zero_le _)
  refine ⟨n, fun i => g (e i), fun i => e i, ?_, ?_, ?_, ?_⟩
  ·
    show g (e 0) = 1
    rw [he0, hS.g_zero]
  ·
    intro i hi
    have := hS.delta (e i) (he_mem i) (e i) (he_mem i)
    rw [if_pos rfl] at this
    have h0 : qcoeff N (-((e i : ℕ) : ℤ)) (g (e i)) = 0 := by
      have hi' : g (e i) = 0 := hi
      rw [hi', map_zero]
    rw [h0] at this
    exact zero_ne_one this
  ·
    intro i σ
    exact hS.galois_smul_eq N (e i) (he_mem i) σ
  · intro k hk
    refine ⟨?_, ?_⟩
    ·
      refine linearIndependent_of_dual_delta (fun i : {i : Fin (n + 1) // e i ≤ k} => g (e i.1))
        (fun i => qcoeff N (-((e i.1 : ℕ) : ℤ))) fun i j => ?_
      rw [hS.delta (e i.1) (he_mem _) (e j.1) (he_mem _)]
      by_cases h : i = j
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg fun h' => h (Subtype.ext (e.injective h'))]
    ·
      have hset : Set.range (fun i : {i : Fin (n + 1) // e i ≤ k} => g (e i.1))
          = g '' (↑(T.filter (· ≤ k)) : Set ℕ) := by
        ext y
        constructor
        · rintro ⟨⟨i, hi⟩, rfl⟩
          exact ⟨e i, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨he_mem i, hi⟩), rfl⟩
        · rintro ⟨q, hq, rfl⟩
          obtain ⟨hqT, hqk⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          obtain ⟨i, rfl⟩ : q ∈ Set.range e := by rw [he_range]; exact Finset.mem_coe.mpr hqT
          exact ⟨⟨i, hqk⟩, rfl⟩
      show Submodule.span _ (Set.range (fun i : {i : Fin (n + 1) // e i ≤ k} => g (e i.1))) = W N k
      rw [hset]
      exact hS.span_eq k hk

end ModularCurve.AdaptedFamilyAux

theorem solution (N : ℕ) [NeZero N] (m : ℕ) :
    ∃ (n : ℕ) (f : Fin (n + 1) → modularFunctionFieldBar N) (o : Fin (n + 1) → ℕ),
      f 0 = 1 ∧ (∀ i, f i ≠ 0) ∧
      (∀ (i : Fin (n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        arithmeticGalois (modularFunctionFieldFull N) σ • f i = f i) ∧
      (∀ k ≤ m, LinearIndependent (AlgebraicClosure ℚ)
            (fun i : {i : Fin (n + 1) // o i ≤ k} => f i) ∧
          Submodule.span (AlgebraicClosure ℚ)
              (Set.range (fun i : {i : Fin (n + 1) // o i ≤ k} => f i))
            = riemannRochSpace ((k : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ))) :=
  ModularCurve.AdaptedFamilyAux.main N m

end
end S_ModularCurve_exists_adapted_family_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_exists_adapted_family_modularFunctionFieldBar (solution)
