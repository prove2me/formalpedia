-- Prove2me | solution 1 for ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d19d4cdd-ecdb-5779-8d3c-2e6a4340b3e2

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable
import Theorems.Thm_ModularCurve_theta_mul
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open Polynomial IntermediateField

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasPrincipalDivisors hasPrincipalDivisors_of_transcendental_of_isSeparable"
p2m_open "AlgebraicCurve"

namespace F10c

section SepCrit

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (δ : Derivation K Ω Ω)
  {x : Ω} (hx : Transcendental K x)

include hx in

private theorem exists_coprime_eq_div (a : K⟮x⟯) :
    ∃ f g : K[X], IsCoprime f g ∧ aeval x g ≠ 0 ∧ (a : Ω) = aeval x f / aeval x g := by
  obtain ⟨u, rfl⟩ := (RatFunc.algEquivOfTranscendental x hx).surjective a
  refine ⟨u.num, u.denom, RatFunc.isCoprime_num_denom u, ?_, ?_⟩
  · intro h
    refine u.denom_ne_zero (transcendental_iff_injective.mp hx ?_)
    rw [h, map_zero]
  · rw [RatFunc.algEquivOfTranscendental_apply]

include hx in

private theorem exists_apply_eq_mul (a : K⟮x⟯) : ∃ b : K⟮x⟯, δ a = (b : Ω) * δ x := by
  obtain ⟨f, g, -, hg, ha⟩ := exists_coprime_eq_div hx a
  refine ⟨⟨aeval x (derivative f * g - f * derivative g) / aeval x (g * g),
    (mem_adjoin_simple_iff K _).mpr ⟨_, _, rfl⟩⟩, ?_⟩
  rw [ha, Derivation.leibniz_div, Derivation.map_aeval, Derivation.map_aeval]
  simp only [smul_eq_mul, map_sub, map_mul]
  field_simp

include hx in

private theorem exists_eq_pow [PerfectField K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hδ : δ x ≠ 0) (a : K⟮x⟯) (ha : δ a = 0) : ∃ c : K⟮x⟯, a = c ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨f, g, hcop, hg, hafg⟩ := exists_coprime_eq_div hx a
  have hinj := transcendental_iff_injective.mp hx

  have hkey : g * derivative f = f * derivative g := by
    rw [hafg, Derivation.leibniz_div, Derivation.map_aeval, Derivation.map_aeval] at ha
    simp only [smul_eq_mul] at ha
    have h2 : aeval x g * (aeval x (derivative f) * δ x) - aeval x f * (aeval x (derivative g) * δ x)
        = 0 := by
      rcases mul_eq_zero.mp ha with h | h
      · exact absurd h (pow_ne_zero _ (inv_ne_zero hg))
      · exact h
    have h3 : (aeval x (g * derivative f) - aeval x (f * derivative g)) * δ x = 0 := by
      rw [map_mul, map_mul, ← h2]; ring
    rcases mul_eq_zero.mp h3 with h | h
    · exact hinj (sub_eq_zero.mp h)
    · exact absurd h hδ

  have hderiv : ∀ {f g : K[X]}, IsCoprime f g → g * derivative f = f * derivative g →
      derivative f = 0 := by
    intro f g hcop hkey
    by_contra hne
    have hdvd : f ∣ derivative f :=
      hcop.dvd_of_dvd_mul_left ⟨derivative g, by rw [← hkey, mul_comm]⟩
    have hf0 : f ≠ 0 := fun h => hne (by rw [h, derivative_zero])
    exact (not_le.mpr (degree_derivative_lt hf0)) (degree_le_of_dvd hdvd hne)
  have hf' : derivative f = 0 := hderiv hcop hkey
  have hg' : derivative g = 0 := hderiv hcop.symm hkey.symm

  have hroot : ∀ {f : K[X]}, derivative f = 0 →
      f = (map ((frobeniusEquiv K p).symm : K →+* K) (contract p f)) ^ p := by
    intro f hf
    rw [← map_frobenius_expand, map_expand, Polynomial.map_map]
    have hcomp : (frobenius K p).comp ((frobeniusEquiv K p).symm : K →+* K) = RingHom.id K :=
      RingHom.ext fun y => frobenius_apply_frobeniusEquiv_symm K p y
    rw [hcomp, Polynomial.map_id, expand_contract p hf hp]
  obtain ⟨f₁, hf1⟩ : ∃ f₁ : K[X], f = f₁ ^ p := ⟨_, hroot hf'⟩
  obtain ⟨g₁, hg1⟩ : ∃ g₁ : K[X], g = g₁ ^ p := ⟨_, hroot hg'⟩
  refine ⟨⟨aeval x f₁ / aeval x g₁, (mem_adjoin_simple_iff K _).mpr ⟨_, _, rfl⟩⟩, Subtype.ext ?_⟩
  rw [IntermediateField.coe_pow]
  show (a : Ω) = (aeval x f₁ / aeval x g₁) ^ p
  rw [hafg, div_pow, ← map_pow, ← map_pow, ← hf1, ← hg1]

include hx in

private theorem isSeparable_of_derivation [PerfectField K] (hδ : δ x ≠ 0) {y : Ω}
    (hy : IsIntegral K⟮x⟯ y) : IsSeparable K⟮x⟯ y := by
  obtain ⟨p, hchar⟩ := ExpChar.exists K
  rcases hchar with _ | ⟨hprime⟩
  ·
    haveI : CharZero K⟮x⟯ :=
      charZero_of_injective_algebraMap (algebraMap K K⟮x⟯).injective
    exact (minpoly.irreducible hy).separable
  haveI := Fact.mk hprime
  haveI : CharP K⟮x⟯ p := charP_of_injective_algebraMap (algebraMap K K⟮x⟯).injective p
  have hp1 : p ≠ 1 := hprime.ne_one
  have hp0 : p ≠ 0 := hprime.ne_zero
  by_contra hsep
  set m := minpoly K⟮x⟯ y with hm
  have hirr : Irreducible m := minpoly.irreducible hy
  have hmonic : m.Monic := minpoly.monic hy
  have hm' : derivative m = 0 := by
    by_contra h
    exact hsep ((separable_iff_derivative_ne_zero hirr).mpr h)

  choose b hb using fun i => exists_apply_eq_mul δ hx (m.coeff i)
  have hcoeff_mul : ∀ i : ℕ, (algebraMap K⟮x⟯ Ω (m.coeff i)) * (i : Ω) = 0 := by
    intro i
    rcases i with - | k
    · simp
    · have h := coeff_derivative m k
      rw [hm', coeff_zero] at h
      rw [← map_natCast (algebraMap K⟮x⟯ Ω), ← map_mul, Nat.cast_succ, ← h, map_zero]

  have haeval : ∑ i ∈ Finset.range (m.natDegree + 1),
      algebraMap K⟮x⟯ Ω (m.coeff i) * y ^ i = 0 := by
    have h := minpoly.aeval K⟮x⟯ y
    rw [aeval_eq_sum_range] at h
    simpa only [Algebra.smul_def] using h
  have hδsum : δ x * ∑ i ∈ Finset.range (m.natDegree + 1), (b i : Ω) * y ^ i = 0 := by
    have h := congrArg δ haeval
    rw [map_zero, map_sum] at h
    rw [Finset.mul_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hbi : δ (algebraMap K⟮x⟯ Ω (m.coeff i)) = (b i : Ω) * δ x := hb i
    rw [Derivation.leibniz, Derivation.leibniz_pow, hbi, smul_eq_mul, smul_eq_mul, nsmul_eq_mul,
      smul_eq_mul]
    have := hcoeff_mul i

    calc δ x * ((b i : Ω) * y ^ i)
        = 0 + y ^ i * ((b i : Ω) * δ x) := by ring
      _ = algebraMap K⟮x⟯ Ω (m.coeff i) * (i : Ω) * (y ^ (i - 1) * δ y)
            + y ^ i * ((b i : Ω) * δ x) := by rw [this, zero_mul]
      _ = algebraMap K⟮x⟯ Ω (m.coeff i) * ((i : Ω) * (y ^ (i - 1) * δ y))
            + y ^ i * ((b i : Ω) * δ x) := by ring
  have hsum : ∑ i ∈ Finset.range (m.natDegree + 1), (b i : Ω) * y ^ i = 0 := by
    rcases mul_eq_zero.mp hδsum with h | h
    · exact absurd h hδ
    · exact h

  have hbtop : b m.natDegree = 0 := by
    have h := hb m.natDegree
    rw [hmonic.coeff_natDegree, OneMemClass.coe_one, Derivation.map_one_eq_zero] at h
    rcases mul_eq_zero.mp h.symm with h | h
    · exact_mod_cast h
    · exact absurd h hδ
  rw [Finset.sum_range_succ, hbtop, ZeroMemClass.coe_zero, zero_mul, add_zero] at hsum

  set q : K⟮x⟯[X] := ∑ i ∈ Finset.range m.natDegree, C (b i) * X ^ i with hq
  have hqy : aeval y q = 0 := by
    rw [hq, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, IntermediateField.algebraMap_apply]
  have hq0 : q = 0 := by
    by_contra hq0
    have h1 : m.degree ≤ q.degree := minpoly.degree_le_of_ne_zero K⟮x⟯ y hq0 hqy
    have h2 : q.degree < m.degree := by
      rw [hq, degree_eq_natDegree hirr.ne_zero]
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i hi => ?_
      exact lt_of_le_of_lt (degree_C_mul_X_pow_le i (b i))
        (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
    exact (not_le.mpr h2) h1
  have hb0 : ∀ i, i < m.natDegree → b i = 0 := by
    intro i hi
    have h := congrArg (fun r : K⟮x⟯[X] => r.coeff i) hq0
    simp only [hq, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at h
    rwa [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hi)] at h
  have hδcoeff : ∀ i, δ (m.coeff i) = 0 := by
    intro i
    rcases lt_trichotomy i m.natDegree with hi | rfl | hi
    · rw [hb i, hb0 i hi, ZeroMemClass.coe_zero, zero_mul]
    · rw [hb, hbtop, ZeroMemClass.coe_zero, zero_mul]
    · rw [coeff_eq_zero_of_natDegree_lt hi, ZeroMemClass.coe_zero, map_zero]

  choose c hc using fun i => exists_eq_pow δ hx hδ (m.coeff i) (hδcoeff i)
  set m₀ := contract p m with hm₀
  have hexp : expand K⟮x⟯ p m₀ = m := expand_contract p hm' hp0
  set h : K⟮x⟯[X] := ∑ i ∈ Finset.range (m₀.natDegree + 1), C (c (i * p)) * X ^ i with hh
  have hfrob : map (frobenius K⟮x⟯ p) h = m₀ := by
    ext n
    rw [coeff_map, frobenius_def, hh, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hn
    · rw [← hc, hm₀, coeff_contract hp0]
    · rw [zero_pow hp0, coeff_eq_zero_of_natDegree_lt (by omega)]
  have hpow : m = h ^ p := by
    rw [← hexp, ← hfrob, ← map_expand, map_frobenius_expand]
  exact not_irreducible_pow hp1 (hpow ▸ hirr)

end SepCrit

section Adjoin

variable (K : Type*) [Field K] {LF : Type*} [Field LF] [Algebra K LF]

private theorem hasPrincipalDivisors_adjoin (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral K⟮x⟯ t)
    (hsep : ∀ y : LF, IsIntegral K⟮x⟯ y → IsSeparable K⟮x⟯ y) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) := by
  set F : IntermediateField K LF := IntermediateField.adjoin K (insert x (T : Set LF)) with hF
  have hxF : x ∈ F := subset_adjoin K _ (Set.mem_insert x _)
  have hTF : ∀ t ∈ T, t ∈ F := fun t ht => subset_adjoin K _ (Set.mem_insert_of_mem x ht)
  set x' : F := ⟨x, hxF⟩ with hx'

  have hx't : Transcendental K x' :=
    (transcendental_algebraMap_iff (R := K) (S := F) (A := LF) Subtype.val_injective).mp hx

  set A : IntermediateField K F := IntermediateField.adjoin K ({x'} : Set F) with hA
  have hliftA : lift A = K⟮x⟯ := by
    rw [hA, lift_adjoin_simple]
  let e : A ≃ₐ[K] K⟮x⟯ := (liftAlgEquiv A).trans (equivOfEq hliftA)
  have he : ∀ a : A, ((e a : K⟮x⟯) : LF) = ((a : F) : LF) := by
    intro a; rfl
  have hcomp : (algebraMap K⟮x⟯ LF).comp (e : A →+* K⟮x⟯) = (RingHom.id LF).comp (algebraMap A LF) :=
    RingHom.ext fun a => he a
  have hcomp' : (algebraMap A LF).comp (e.symm : K⟮x⟯ →+* A)
      = (RingHom.id LF).comp (algebraMap K⟮x⟯ LF) := by
    ext b
    change (((e.symm b : A) : F) : LF) = ((b : K⟮x⟯) : LF)
    rw [← he (e.symm b), AlgEquiv.apply_symm_apply]

  have hint : ∀ t (ht : t ∈ T), IsIntegral A (⟨t, hTF t ht⟩ : F) := by
    intro t ht
    have h1 : IsIntegral A (t : LF) :=
      (hT t ht).map_of_comp_eq (R := K⟮x⟯) (S := LF) (T := A) (U := LF)
        (e.symm : K⟮x⟯ →+* A) (RingHom.id LF) hcomp'
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A F LF) Subtype.val_injective).mp h1

  haveI : FiniteDimensional A F := by
    set T' : Set F := (fun t : T => (⟨(t : LF), hTF t t.2⟩ : F)) '' Set.univ with hT'
    haveI : Finite T' := Set.Finite.to_subtype ((Set.finite_univ).image _)
    have hT'int : ∀ y ∈ T', IsIntegral A y := by
      rintro _ ⟨t, -, rfl⟩; exact hint t t.2
    haveI : FiniteDimensional A (IntermediateField.adjoin A T') := finiteDimensional_adjoin hT'int
    have htop : IntermediateField.adjoin A T' = ⊤ := by
      apply restrictScalars_injective K
      rw [restrictScalars_adjoin, restrictScalars_top]
      apply lift_injective
      rw [lift_top, lift_adjoin]
      apply le_antisymm (adjoin_le_iff.mpr ?_) ?_
      · rintro _ ⟨y, hy, rfl⟩; exact y.2
      · show IntermediateField.adjoin K (insert x (T : Set LF)) ≤ _
        apply adjoin.mono
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨x', Or.inl (subset_adjoin K _ (Set.mem_singleton _)), rfl⟩
        · exact ⟨⟨z, hTF z hz⟩, Or.inr ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩, rfl⟩
    rw [htop] at this
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := A) (E := F)).toLinearEquiv

  haveI : Algebra.IsSeparable A F := ⟨fun z => by
    have hzLF : IsIntegral K⟮x⟯ ((z : F) : LF) :=
      ((IsIntegral.of_finite A z).map (IsScalarTower.toAlgHom A F LF)).map_of_comp_eq
        (R := A) (S := LF) (T := K⟮x⟯) (U := LF) (e : A →+* K⟮x⟯) (RingHom.id LF) hcomp
    have h2 : IsSeparable A ((z : F) : LF) :=
      IsSeparable.of_equiv_equiv (e.symm : K⟮x⟯ ≃+* A) (RingEquiv.refl LF) hcomp' (hsep _ hzLF)
    exact IsSeparable.of_algHom (IsScalarTower.toAlgHom A F LF) h2⟩
  exact hasPrincipalDivisors_of_transcendental_of_isSeparable hx't inferInstance inferInstance

end Adjoin

section Theta

variable (K : Type*) [Field K]

private theorem theta_algebraMap (c : K) :
    (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K)
      * LaurentSeries.derivative K (algebraMap K (LaurentSeries K) c) = 0 := by
  ext k
  rw [ModularCurve.theta_coeff, HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_zero]
  split_ifs with hk
  · subst hk; exact zero_smul ℤ c
  · exact smul_zero k

private abbrev instModuleLS : Module K (LaurentSeries K) := Algebra.toModule

attribute [local instance 2000] instModuleLS

private abbrev Der : Type _ :=
  @Derivation K (LaurentSeries K) (LaurentSeries K) _ _ _ _ _ Algebra.toModule

private def theta : Der K where
  toFun f := (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K f
  map_add' f g := by simp only [map_add, mul_add]
  map_smul' c f := by
    dsimp only [RingHom.id_apply]
    rw [Algebra.smul_def, Algebra.smul_def, ModularCurve.theta_mul, theta_algebraMap, mul_zero, add_zero]
  map_one_eq_zero' := by
    show (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K 1 = 0
    ext k
    rw [ModularCurve.theta_coeff]
    by_cases hk : k = 0
    · subst hk; simp
    · simp [hk]
  leibniz' f g := by
    show (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K (f * g)
      = f • ((HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K g)
        + g • ((HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K f)
    rw [smul_eq_mul, smul_eq_mul]
    exact ModularCurve.theta_mul f g

private theorem theta_apply (f : LaurentSeries K) :
    theta K f = (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K f :=
  rfl

private theorem theta_jqModC_ne_zero : theta K (ModularCurve.jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : LaurentSeries K => f.coeff (-1)) h
  simp only [theta_apply, ModularCurve.theta_coeff, ModularCurve.coeff_jqModC_neg_one] at h1
  simp at h1

end Theta

end F10c

end AlgebraicCurve

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField.AlgebraicCurve ModularCurve"

theorem solution (K : Type*) [Field K] [PerfectField K] (N : ℕ) [NeZero N] :
    HasPrincipalDivisors K (modularFunctionFieldC K N) := by
  have h : modularFunctionFieldC K N = IntermediateField.adjoin K
      (insert (jqModC K) ((({jqNModC K N} : Finset _) : Set (LaurentSeries K)))) := by
    rw [Finset.coe_singleton]; rfl
  rw [h]
  refine F10c.hasPrincipalDivisors_adjoin K (jqModC K) (transcendental_jqModC K) {jqNModC K N} ?_ ?_
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    exact isIntegral_jqNModC_all K N
  · intro y hy
    exact F10c.isSeparable_of_derivation (F10c.theta K) (transcendental_jqModC K)
      (F10c.theta_jqModC_ne_zero K) hy

example : ∀ (K : Type*) [Field K] [PerfectField K] (N : ℕ) [NeZero N],
    HasPrincipalDivisors K (modularFunctionFieldC K N) := @solution

#print axioms solution

end
end S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
end P2MW
export P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField (solution)
