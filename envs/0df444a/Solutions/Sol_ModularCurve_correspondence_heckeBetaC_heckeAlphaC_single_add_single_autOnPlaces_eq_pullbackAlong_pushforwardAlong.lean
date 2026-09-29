-- Prove2me | solution 1 for ModularCurve.correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/724c522e-c3e7-5d18-b5e9-4cf25aceea93

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace RibetUsWs

section Generic

variable {k : Type*} [Field k]

theorem finrankAlong_inclusion {E : Type*} [Field E] [Algebra k E] {A B : IntermediateField k E}
    (h : A ≤ B) : finrankAlong k (IntermediateField.inclusion h) = A.relfinrank B := by
  rw [finrankAlong_eq_relfinrank_fieldRange]
  have hval : B.val.comp (IntermediateField.inclusion h) = A.val := by
    ext x
    rfl
  rw [hval, IntermediateField.fieldRange_val]

theorem finiteAlong_of_finrankAlong_pos {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (h : 0 < finrankAlong k φ) : FiniteAlong k φ := by
  letI := algebraAlong φ
  exact Module.finite_of_finrank_pos h

theorem isIntegral_of_finiteAlong {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hfin : FiniteAlong k φ) : φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := hfin
  exact (Algebra.IsIntegral.of_finite F F').isIntegral

theorem intermediateField_eq_top_of_generators {E : Type*} [Field E] [Algebra k E]
    (Z : IntermediateField k E) (E' : IntermediateField k Z)
    (S₀ : Set E) (hZ : Z ≤ IntermediateField.adjoin k S₀)
    (hS₀ : ∀ s ∈ S₀, ∃ a ∈ E', (a : E) = s) : E' = ⊤ := by
  have hmap : IntermediateField.adjoin k S₀ ≤ E'.map Z.val := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro s hs
    obtain ⟨a, ha, rfl⟩ := hS₀ s hs
    exact ⟨a, ha, rfl⟩
  refine top_le_iff.mp fun z _ => ?_
  obtain ⟨e, he, hez⟩ := hmap (hZ z.2)
  exact (Subtype.ext hez : e = z) ▸ he

theorem restrictAlong_id {F : Type*} [Field F] [Algebra k F] (h : (AlgHom.id k F).toRingHom.IsIntegral)
    (W : Place k F) : W.restrictAlong (AlgHom.id k F) h = W := by
  apply Place.ext
  refine SetLike.ext fun x => ?_
  exact Iff.rfl

theorem ramificationIndexAlong_id {F : Type*} [Field F] [Algebra k F] (W : Place k F) :
    Place.ramificationIndexAlong (AlgHom.id k F) W = 1 := by
  letI := algebraAlong (AlgHom.id k F)
  show W.ramificationIndex F = 1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  have h1 : (1 : ℕ) ∈ {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (algebraMap F F f) = n} :=
    ⟨Nat.one_pos, π, hπ0, by exact_mod_cast W.ord_coe_irreducible hπ⟩
  unfold Place.ramificationIndex
  exact le_antisymm (Nat.sInf_le h1) (Nat.sInf_mem ⟨1, h1⟩).1

theorem pullbackAlong_id {F : Type*} [Field F] [Algebra k F] [HasPrincipalDivisors k F]
    (h : (AlgHom.id k F).toRingHom.IsIntegral) (D : Divisor k F) :
    Divisor.pullbackAlong (AlgHom.id k F) h D = D := by
  refine Finsupp.ext fun W => ?_
  rw [Divisor.pullbackAlong_apply, ramificationIndexAlong_id, restrictAlong_id]
  simp

section Symm

variable {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F'] (e : F ≃ₐ[k] F')

theorem isIntegral_symm : (e.symm.toAlgHom : F' →ₐ[k] F).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ e.symm.surjective

theorem restrictAlong_symm (h : (e.symm.toAlgHom : F' →ₐ[k] F).toRingHom.IsIntegral) (x : Place k F) :
    x.restrictAlong e.symm.toAlgHom h = Place.congrEquiv e.toRingEquiv (fun c => e.commutes c) x := by
  apply Place.ext
  refine SetLike.ext fun y => ?_
  exact Iff.rfl

theorem inertiaDegAlong_symm (h : (e.symm.toAlgHom : F' →ₐ[k] F).toRingHom.IsIntegral) (x : Place k F) :
    x.inertiaDegAlong e.symm.toAlgHom h = 1 := by
  letI := algebraAlong (e.symm.toAlgHom : F' →ₐ[k] F)
  haveI := isScalarTower_along (e.symm.toAlgHom : F' →ₐ[k] F)
  haveI := isIntegral_along _ h
  show x.inertiaDeg F' = 1
  unfold Place.inertiaDeg
  have hsurj : Function.Surjective (algebraMap (x.restrict F').ResidueField x.ResidueField) := by
    intro r
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
    have hy : e y ∈ (x.restrict F').toValuationSubring := by
      rw [Place.mem_restrict_iff]
      show e.symm (e y) ∈ x.toValuationSubring
      rw [e.symm_apply_apply]
      exact y.2
    refine ⟨IsLocalRing.residue _ ⟨e y, hy⟩, ?_⟩
    rw [Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue]
    congr 1
    ext
    show e.symm (e y) = y
    exact e.symm_apply_apply y
  let L := LinearEquiv.ofBijective (Algebra.linearMap (x.restrict F').ResidueField x.ResidueField)
    ⟨fun a b hab => (algebraMap (x.restrict F').ResidueField x.ResidueField).injective hab, fun r => hsurj r⟩
  rw [← L.finrank_eq, Module.finrank_self]

theorem pushforwardAlong_symm_single (h : (e.symm.toAlgHom : F' →ₐ[k] F).toRingHom.IsIntegral)
    (x : Place k F) (n : ℤ) :
    Divisor.pushforwardAlong e.symm.toAlgHom h (Finsupp.single x n)
      = Finsupp.single (Place.congrEquiv e.toRingEquiv (fun c => e.commutes c) x) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_symm, restrictAlong_symm]
  simp

theorem finrankAlong_symm : finrankAlong k (e.symm.toAlgHom : F' →ₐ[k] F) = 1 := by
  letI := algebraAlong (e.symm.toAlgHom : F' →ₐ[k] F)
  show Module.finrank F' F = 1
  let L : F' ≃ₗ[F'] F := e.symm.toRingEquiv.toAddEquiv.toLinearEquiv fun c y => by
    show e.symm (c * y) = e.symm c * e.symm y
    exact map_mul e.symm c y
  rw [← L.finrank_eq, Module.finrank_self]

theorem finiteAlong_symm : FiniteAlong k (e.symm.toAlgHom : F' →ₐ[k] F) :=
  finiteAlong_of_finrankAlong_pos _ (by rw [finrankAlong_symm]; exact Nat.one_pos)

theorem separableAlong_symm : SeparableAlong k (e.symm.toAlgHom : F' →ₐ[k] F) := by
  letI := algebraAlong (e.symm.toAlgHom : F' →ₐ[k] F)
  show Algebra.IsSeparable F' F
  refine ⟨fun y => ?_⟩
  have hy : y = algebraMap F' F (e y) := (e.symm_apply_apply y).symm
  rw [hy]
  exact isSeparable_algebraMap (e y)

end Symm

theorem isSeparable_along_inclusion {E : Type*} [Field E] [Algebra k E] (J A B : IntermediateField k E)
    (hJA : J ≤ A) (hAB : A ≤ B) (t : E) (ht : t ∈ B) (hsep : IsSeparable J t) :
    letI := algebraAlong (IntermediateField.inclusion hAB)
    IsSeparable A (⟨t, ht⟩ : B) := by
  letI := algebraAlong (IntermediateField.inclusion hAB)
  set P := minpoly J t with hPdef
  have hP : P.Separable := hsep
  let i : J →+* A := (IntermediateField.inclusion hJA).toRingHom
  have hQ : (P.map i).Separable := hP.map
  have hQ0 : Polynomial.aeval (⟨t, ht⟩ : B) (P.map i) = 0 := by
    apply Subtype.val_injective
    rw [Polynomial.aeval_def]
    show B.val.toRingHom (Polynomial.eval₂ (algebraMap A B) (⟨t, ht⟩ : B) (P.map i)) = ((0 : B) : E)
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
    have hcomp : (B.val.toRingHom.comp (algebraMap A B)).comp i = algebraMap J E := RingHom.ext fun _ => rfl
    rw [hcomp]
    show Polynomial.aeval t P = 0
    exact minpoly.aeval J t
  exact hQ.of_dvd (minpoly.dvd A _ hQ0)

set_option synthInstance.maxHeartbeats 1600000 in

theorem separableAlong_inclusion_of_generators {E : Type*} [Field E] [Algebra k E]
    (J A B : IntermediateField k E) (hJA : J ≤ A) (hAB : A ≤ B) (T : Set E) (hT : ∀ t ∈ T, t ∈ B)
    (hgen : B ≤ IntermediateField.adjoin k ((A : Set E) ∪ T)) (hsep : ∀ t ∈ T, IsSeparable J t) :
    SeparableAlong k (IntermediateField.inclusion hAB) := by
  letI := algebraAlong (IntermediateField.inclusion hAB)
  haveI := isScalarTower_along (IntermediateField.inclusion hAB)
  show Algebra.IsSeparable A B
  let S : Set B := {b | (b : E) ∈ T}
  have hS : IntermediateField.adjoin A S = ⊤ := by
    let W : IntermediateField k E := ((IntermediateField.adjoin A S).restrictScalars k).map B.val
    have hAW : (A : Set E) ∪ T ⊆ W := by
      rintro x (hx | hx)
      · refine (IntermediateField.mem_map _).mpr ⟨algebraMap A B ⟨x, hx⟩, ?_, rfl⟩
        exact (IntermediateField.mem_restrictScalars k).mpr (IntermediateField.algebraMap_mem _ _)
      · refine (IntermediateField.mem_map _).mpr ⟨⟨x, hT x hx⟩, ?_, rfl⟩
        exact (IntermediateField.mem_restrictScalars k).mpr
          (IntermediateField.subset_adjoin _ _ (show (⟨x, hT x hx⟩ : B) ∈ S from hx))
    have hle : IntermediateField.adjoin k ((A : Set E) ∪ T) ≤ W := IntermediateField.adjoin_le_iff.mpr hAW
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨w, hw, hwz⟩ := (IntermediateField.mem_map _).mp (hle (hgen z.2))
    have hwz' : w = z := Subtype.ext hwz
    rw [← hwz']
    exact (IntermediateField.mem_restrictScalars k).mp hw
  have hsepS : ∀ b ∈ S, IsSeparable A b := by
    rintro ⟨b, hb⟩ hbS
    exact isSeparable_along_inclusion J A B hJA hAB b hb (hsep b hbS)
  haveI : Algebra.IsSeparable A (IntermediateField.adjoin A S) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable A B).mpr hsepS
  rw [hS] at this
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv : (⊤ : IntermediateField A B) ≃ₐ[A] B)

theorem dedekindPsi_ne_zero (m : ℕ) (hm : m ≠ 0) : dedekindPsi m ≠ 0 := by
  have h1 : (1 : ℕ) ∈ m.divisors.filter Squarefree :=
    Finset.mem_filter.2 ⟨Nat.one_mem_divisors.2 hm, squarefree_one⟩
  have hle : m / 1 ≤ dedekindPsi m := by
    unfold dedekindPsi
    exact Finset.single_le_sum (f := fun d => m / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at hle
  exact Nat.pos_iff_ne_zero.1 ((Nat.pos_of_ne_zero hm).trans_le hle)

end Generic

section Modular

variable {k : Type*} [Field k]

theorem natCast_ne_zero_of_not_dvd (p n : ℕ) [CharP k p] (h : ¬ p ∣ n) : ((n : ℕ) : k) ≠ 0 :=
  fun h0 => h ((CharP.cast_eq_zero_iff k p n).mp h0)

theorem not_dvd_mul_mul_self (p M s : ℕ) [NeZero M] [NeZero s] (hp0 : p.Prime ∨ p = 0) (hp : ¬ p ∣ M * s) :
    ¬ p ∣ M * s * s := by
  rcases hp0 with hpr | rfl
  · intro h
    rcases hpr.dvd_mul.mp h with h1 | h1
    · exact hp h1
    · exact hp (h1.trans (Nat.dvd_mul_left s M))
  · intro h
    rw [zero_dvd_iff] at h
    exact NeZero.ne (M * s * s) h

theorem coprime_of_prime_not_dvd {M s : ℕ} (hs : s.Prime) (hsM : ¬ s ∣ M) : Nat.Coprime M s :=
  ((Nat.Prime.coprime_iff_not_dvd hs).mpr hsM).symm

theorem finrankAlong_levelAlphaC (M s : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hsM : ¬ s ∣ M) (p : ℕ)
    [CharP k p] (hp : ¬ p ∣ M * s) (hM : jqNModC k M ∈ modularFunctionFieldC k (M * s)) :
    finrankAlong k (levelAlphaC k M s hM) = s + 1 := by
  have hpM : ¬ p ∣ M := fun h => hp (h.mul_right s)
  have hcast : ((M * s : ℕ) : k) ≠ 0 := natCast_ne_zero_of_not_dvd p _ hp
  have h0 := finrankAlong_inclusion (k := k) (modularFunctionFieldC_le_of_mem k M s hM)
  refine (show finrankAlong k (levelAlphaC k M s hM)
    = (modularFunctionFieldC k M).relfinrank (modularFunctionFieldC k (M * s)) from h0).trans ?_
  rw [modularFunctionFieldC_eq_modularFunctionFieldFullC k p M hpM,
    modularFunctionFieldC_eq_modularFunctionFieldFullC k p (M * s) hp]
  have h1 := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k M s hcast).1
  rw [dedekindPsi_mul_of_coprime M s (coprime_of_prime_not_dvd hs hsM), dedekindPsi_prime hs] at h1
  have hpos : 0 < dedekindPsi M := Nat.pos_of_ne_zero (dedekindPsi_ne_zero M (NeZero.ne M))
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, Nat.mul_comm]

theorem finrankAlong_heckeAlphaC (M s : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hsM : ¬ s ∣ M) (p : ℕ)
    [CharP k p] (hp : ¬ p ∣ M * s) (hp0 : p.Prime ∨ p = 0) :
    finrankAlong k (heckeAlphaC k (M * s) s) = s := by
  have hpss := not_dvd_mul_mul_self p M s hp0 hp
  have hcast : ((M * s * s : ℕ) : k) ≠ 0 := natCast_ne_zero_of_not_dvd p _ hpss
  have h0 := finrankAlong_inclusion (k := k) (modularFunctionFieldC_le_charLDegeneracyRoof k (M * s) s)
  refine (show finrankAlong k (heckeAlphaC k (M * s) s)
    = (modularFunctionFieldC k (M * s)).relfinrank (charLDegeneracyRoof k (M * s) s) from h0).trans ?_
  rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k p (M * s) s hpss,
    modularFunctionFieldC_eq_modularFunctionFieldFullC k p (M * s) hp]
  have h1 := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k (M * s) s hcast).1
  have hcop : Nat.Coprime M s := coprime_of_prime_not_dvd hs hsM
  have hψ1 : dedekindPsi (M * s) = dedekindPsi M * (s + 1) := by
    rw [dedekindPsi_mul_of_coprime M s hcop, dedekindPsi_prime hs]
  have hψ2 : dedekindPsi (M * s * s) = dedekindPsi M * (s * (s + 1)) := by
    have h22 : s ^ 2 + s ^ (2 - 1) = s * (s + 1) := by norm_num; ring
    rw [Nat.mul_assoc, dedekindPsi_mul_of_coprime M (s * s) (Nat.Coprime.mul_right hcop hcop), ← pow_two,
      dedekindPsi_prime_pow s 2 hs two_ne_zero, h22]
  rw [hψ1, hψ2] at h1
  have hpos : 0 < dedekindPsi M * (s + 1) :=
    Nat.mul_pos (Nat.pos_of_ne_zero (dedekindPsi_ne_zero M (NeZero.ne M))) (Nat.succ_pos s)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1]
  ring

theorem levelBetaC_eq_aut_levelAlphaC (M s : ℕ) [NeZero M] [NeZero s]
    (hM : jqNModC k M ∈ modularFunctionFieldC k (M * s)) (hS : jqNModC k s ∈ modularFunctionFieldC k (M * s))
    (σ : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (hσ : IsAtkinLehnerLevelAut k M s hM hS σ) (x : modularFunctionFieldC k M) :
    levelBetaC k M s hS x = σ (levelAlphaC k M s hM x) := by
  let A : Subalgebra k (modularFunctionFieldC k M) :=
    AlgHom.equalizer (levelBetaC k M s hS) (σ.toAlgHom.comp (levelAlphaC k M s hM))
  have hinv : ∀ a ∈ A, a⁻¹ ∈ A := by
    intro a ha
    rw [AlgHom.mem_equalizer] at ha ⊢
    rw [map_inv₀, map_inv₀, ha]
  let E' : IntermediateField k (modularFunctionFieldC k M) := A.toIntermediateField hinv
  have hE' : E' = ⊤ := by
    refine intermediateField_eq_top_of_generators _ E' {jqModC k, jqNModC k M} le_rfl ?_
    intro t ht
    rcases ht with rfl | ht
    · refine ⟨jGeomGen k M, ?_, rfl⟩
      change jGeomGen k M ∈ A
      rw [AlgHom.mem_equalizer]
      apply Subtype.ext
      have e1 : levelAlphaC k M s hM (jGeomGen k M) = jGeomGen k (M * s) := Subtype.ext rfl
      show qExpand k s (jqModC k) = ((σ (levelAlphaC k M s hM (jGeomGen k M)) : _) : LaurentSeries k)
      rw [e1, hσ.1]
      rfl
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      refine ⟨jNGeomGen k M, ?_, rfl⟩
      change jNGeomGen k M ∈ A
      rw [AlgHom.mem_equalizer]
      apply Subtype.ext
      have e1 : levelAlphaC k M s hM (jNGeomGen k M) = ⟨jqNModC k M, hM⟩ := Subtype.ext rfl
      show qExpand k s (jqNModC k M) = ((σ (levelAlphaC k M s hM (jNGeomGen k M)) : _) : LaurentSeries k)
      rw [e1, hσ.2.2.2]
      show qExpand k s (qExpand k M (jqModC k)) = jqNModC k (M * s)
      rw [qExpand_qExpand]
      exact qExpand_congr (Nat.mul_comm s M) _
  have hx : x ∈ E' := hE' ▸ IntermediateField.mem_top
  exact (AlgHom.mem_equalizer _ _ _).mp hx

theorem adjoin_range_legs_eq_top (N q : ℕ) [NeZero N] [NeZero q] :
    IntermediateField.adjoin k (Set.range (heckeAlphaC k N q) ∪ Set.range (heckeBetaC k N q)) = ⊤ := by
  refine intermediateField_eq_top_of_generators _ _ {jqModC k, jqNModC k N, jqNModC k q, jqNModC k (N * q)}
    le_rfl ?_
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨heckeAlphaC k N q (jGeomGen k N), IntermediateField.subset_adjoin _ _ (Or.inl ⟨_, rfl⟩), rfl⟩
  · exact ⟨heckeAlphaC k N q (jNGeomGen k N), IntermediateField.subset_adjoin _ _ (Or.inl ⟨_, rfl⟩), rfl⟩
  · exact ⟨heckeBetaC k N q (jGeomGen k N), IntermediateField.subset_adjoin _ _ (Or.inr ⟨_, rfl⟩), rfl⟩
  · refine ⟨heckeBetaC k N q (jNGeomGen k N), IntermediateField.subset_adjoin _ _ (Or.inr ⟨_, rfl⟩), ?_⟩
    show qExpand k q (qExpand k N (jqModC k)) = jqNModC k (N * q)
    rw [qExpand_qExpand]
    exact qExpand_congr (Nat.mul_comm q N) _

theorem adjoin_jqModC_le (N : ℕ) [NeZero N] :
    IntermediateField.adjoin k {jqModC k} ≤ modularFunctionFieldC k N :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem k N))

theorem separableAlong_levelAlphaC (M s : ℕ) [NeZero M] [NeZero s]
    (hM : jqNModC k M ∈ modularFunctionFieldC k (M * s)) (hcast : ((M * s : ℕ) : k) ≠ 0) :
    SeparableAlong k (levelAlphaC k M s hM) := by
  refine separableAlong_inclusion_of_generators (IntermediateField.adjoin k {jqModC k}) (modularFunctionFieldC k M)
    (modularFunctionFieldC k (M * s)) (adjoin_jqModC_le M) (modularFunctionFieldC_le_of_mem k M s hM)
    {jqNModC k (M * s)} ?_ ?_ ?_
  · intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact jqNModC_mem k (M * s)
  · refine IntermediateField.adjoin.mono k _ _ ?_
    intro t ht
    rcases ht with rfl | ht
    · exact Or.inl (jqModC_mem k M)
    · exact Or.inr ht
  · intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact isSeparable_jqNModC_of_natCast_ne_zero k (M * s) hcast

theorem separableAlong_heckeAlphaC (N q : ℕ) [NeZero N] [NeZero q] (hq : ((q : ℕ) : k) ≠ 0)
    (hNq : ((N * q : ℕ) : k) ≠ 0) : SeparableAlong k (heckeAlphaC k N q) := by
  refine separableAlong_inclusion_of_generators (IntermediateField.adjoin k {jqModC k}) (modularFunctionFieldC k N)
    (charLDegeneracyRoof k N q) (adjoin_jqModC_le N) (modularFunctionFieldC_le_charLDegeneracyRoof k N q)
    {jqNModC k q, jqNModC k (N * q)} ?_ ?_ ?_
  · intro t ht
    rcases ht with rfl | ht
    · exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inr (Or.inl rfl)))
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inr (Or.inr rfl)))
  · refine IntermediateField.adjoin.mono k _ _ ?_
    intro t ht
    rcases ht with rfl | rfl | rfl | ht
    · exact Or.inl (jqModC_mem k N)
    · exact Or.inl (jqNModC_mem k N)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ht)
  · intro t ht
    rcases ht with rfl | ht
    · exact isSeparable_jqNModC_of_natCast_ne_zero k q hq
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact isSeparable_jqNModC_of_natCast_ne_zero k (N * q) hNq

theorem exists_symm_eq_and_ne (M s : ℕ) [NeZero M] [NeZero s] (hs : s.Prime)
    (hM : jqNModC k M ∈ modularFunctionFieldC k (M * s)) (hS : jqNModC k s ∈ modularFunctionFieldC k (M * s))
    (σ : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (hσ : IsAtkinLehnerLevelAut k M s hM hS σ) :
    ∃ (a : modularFunctionFieldC k (M * s)) (b : modularFunctionFieldC k (M * s)),
      σ.symm.toAlgHom a = AlgHom.id k _ b ∧ heckeAlphaC k (M * s) s a ≠ heckeBetaC k (M * s) s b := by
  refine ⟨jGeomGen k (M * s), ⟨jqNModC k s, hS⟩, ?_, ?_⟩
  · show σ.symm (jGeomGen k (M * s)) = ⟨jqNModC k s, hS⟩
    rw [AlgEquiv.symm_apply_eq]
    exact hσ.2.1.symm
  · intro h
    have h' := congrArg (fun z : charLDegeneracyRoof k (M * s) s => (z : LaurentSeries k).coeff (-1)) h
    change (jqModC k).coeff (-1) = (qExpand k s (jqNModC k s)).coeff (-1) at h'
    rw [coeff_jqModC_neg_one, jqNModC, qExpand_qExpand, qExpand_coeff_of_not_dvd] at h'
    · exact one_ne_zero h'
    · intro hd
      have h1 : ((s * s : ℕ) : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) (dvd_neg.mp hd)
      have h2 : s * s = 1 := by exact_mod_cast h1
      have h3 : s = 1 := Nat.eq_one_of_mul_eq_one_right h2
      exact hs.one_lt.ne' h3

theorem graph_term (M s : ℕ) [NeZero M] [NeZero s]
    (σ : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    [HasPrincipalDivisors k (modularFunctionFieldC k (M * s))]
    (h1 : (σ.symm.toAlgHom : _ →ₐ[k] _).toRingHom.IsIntegral)
    (h2 : (AlgHom.id k (modularFunctionFieldC k (M * s))).toRingHom.IsIntegral)
    (x : Place k (modularFunctionFieldC k (M * s))) :
    Divisor.pushforwardAlong σ.symm.toAlgHom h1
        (Divisor.pullbackAlong (AlgHom.id k _) h2 (Finsupp.single x 1))
      = Finsupp.single (autOnPlaces k M s σ x) 1 := by
  rw [pullbackAlong_id, pushforwardAlong_symm_single]
  rfl

theorem main (M s : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hsM : ¬ s ∣ M)
    (p : ℕ) [CharP k p] (hp : ¬ p ∣ M * s)
    (hM : jqNModC k M ∈ modularFunctionFieldC k (M * s)) (hS : jqNModC k s ∈ modularFunctionFieldC k (M * s))
    (σ : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (hσ : IsAtkinLehnerLevelAut k M s hM hS σ)
    [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
    [HasPrincipalDivisors k ↥(modularFunctionFieldC k (M * s))]
    (hα : HeckeAlphaCIntegral k (M * s) s) (hβ : HeckeBetaCIntegral k (M * s) s)
    (ha : (levelAlphaC k M s hM).toRingHom.IsIntegral) (hb : (levelBetaC k M s hS).toRingHom.IsIntegral)
    (x : Place k ↥(modularFunctionFieldC k (M * s))) :
    Divisor.correspondence (heckeBetaC k (M * s) s) (heckeAlphaC k (M * s) s) hβ hα (Finsupp.single x 1)
        + Finsupp.single (autOnPlaces k M s σ x) 1
      = Divisor.pullbackAlong (levelBetaC k M s hS) hb
          (Divisor.pushforwardAlong (levelAlphaC k M s hM) ha (Finsupp.single x 1)) := by
  have hp0 : p.Prime ∨ p = 0 := CharP.char_is_prime_or_zero k p
  have hpss : ¬ p ∣ M * s * s := not_dvd_mul_mul_self p M s hp0 hp
  have hps : ¬ p ∣ s := fun h => hp (h.trans (Nat.dvd_mul_left s M))
  have hcast : ((M * s : ℕ) : k) ≠ 0 := natCast_ne_zero_of_not_dvd p _ hp
  have hcasts : ((s : ℕ) : k) ≠ 0 := natCast_ne_zero_of_not_dvd p _ hps
  have hcastss : ((M * s * s : ℕ) : k) ≠ 0 := natCast_ne_zero_of_not_dvd p _ hpss

  have hsq : (heckeAlphaC k (M * s) s).comp (levelBetaC k M s hS)
      = (heckeBetaC k (M * s) s).comp (levelAlphaC k M s hM) := by
    refine AlgHom.ext fun y => Subtype.ext ?_
    rw [AlgHom.comp_apply, coe_heckeAlphaC, coe_levelBetaC, AlgHom.comp_apply, coe_heckeBetaC, coe_levelAlphaC]
  have hsq' : (σ.symm.toAlgHom : _ →ₐ[k] _).comp (levelBetaC k M s hS)
      = (AlgHom.id k _).comp (levelAlphaC k M s hM) := by
    refine AlgHom.ext fun y => ?_
    show σ.symm (levelBetaC k M s hS y) = levelAlphaC k M s hM y
    rw [levelBetaC_eq_aut_levelAlphaC M s hM hS σ hσ y, σ.symm_apply_apply]

  have hda : finrankAlong k (levelAlphaC k M s hM) = s + 1 := finrankAlong_levelAlphaC M s hs hsM p hp hM
  have hdα : finrankAlong k (heckeAlphaC k (M * s) s) = s := finrankAlong_heckeAlphaC M s hs hsM p hp hp0
  have hafin : FiniteAlong k (levelAlphaC k M s hM) :=
    finiteAlong_of_finrankAlong_pos _ (by rw [hda]; exact Nat.succ_pos s)
  have hαfin : FiniteAlong k (heckeAlphaC k (M * s) s) :=
    finiteAlong_of_finrankAlong_pos _ (by rw [hdα]; exact hs.pos)
  have hσfin : FiniteAlong k (σ.symm.toAlgHom : _ →ₐ[k] _) := finiteAlong_symm σ
  have hNa : NormFormulaAlong k (levelAlphaC k M s hM) hafin :=
    normFormulaAlong_of_separableAlong _ hafin (separableAlong_levelAlphaC M s hM hcast)
  have hNα : NormFormulaAlong k (heckeAlphaC k (M * s) s) hαfin :=
    normFormulaAlong_of_separableAlong _ hαfin (separableAlong_heckeAlphaC (M * s) s hcasts hcastss)
  have hNσ : NormFormulaAlong k (σ.symm.toAlgHom : _ →ₐ[k] _) hσfin :=
    normFormulaAlong_of_separableAlong _ hσfin (separableAlong_symm σ)
  have hgen' : IntermediateField.adjoin k
      (Set.range (σ.symm.toAlgHom : _ →ₐ[k] _) ∪ Set.range (AlgHom.id k (modularFunctionFieldC k (M * s))))
        = ⊤ :=
    top_le_iff.mp fun y _ => IntermediateField.subset_adjoin _ _ (Or.inr ⟨y, rfl⟩)
  have hdeg : finrankAlong k (heckeAlphaC k (M * s) s) + finrankAlong k (σ.symm.toAlgHom : _ →ₐ[k] _)
      = finrankAlong k (levelAlphaC k M s hM) := by
    rw [hdα, finrankAlong_symm, hda]
  have key := Divisor.pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong
    (levelBetaC k M s hS) (levelAlphaC k M s hM) (heckeAlphaC k (M * s) s) (heckeBetaC k (M * s) s)
    (σ.symm.toAlgHom : _ →ₐ[k] _) (AlgHom.id k _) hsq hsq' hb ha hα hβ (isIntegral_symm σ)
    (RingHom.isIntegral_of_surjective _ Function.surjective_id) hafin hαfin hσfin hNa hNα hNσ
    (adjoin_range_legs_eq_top (M * s) s) hgen' hdeg (exists_symm_eq_and_ne M s hs hM hS σ hσ)
    (Finsupp.single x 1)
  rw [key, Divisor.correspondence_apply, graph_term]

end Modular

end RibetUsWs

theorem solution
    (M s : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] (p : ℕ) [CharP k p] (hp : ¬ p ∣ M * s)
    (hM : jqNModC k M ∈ modularFunctionFieldC k (M * s)) (hS : jqNModC k s ∈ modularFunctionFieldC k (M * s))
    (σ : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (hσ : IsAtkinLehnerLevelAut k M s hM hS σ) :
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
      [HasPrincipalDivisors k ↥(modularFunctionFieldC k (M * s))]
      (hα : HeckeAlphaCIntegral k (M * s) s) (hβ : HeckeBetaCIntegral k (M * s) s)
      (ha : (levelAlphaC k M s hM).toRingHom.IsIntegral) (hb : (levelBetaC k M s hS).toRingHom.IsIntegral)
      (x : Place k ↥(modularFunctionFieldC k (M * s))),
      Divisor.correspondence (heckeBetaC k (M * s) s) (heckeAlphaC k (M * s) s) hβ hα (Finsupp.single x 1)
          + Finsupp.single (autOnPlaces k M s σ x) 1
        = Divisor.pullbackAlong (levelBetaC k M s hS) hb
            (Divisor.pushforwardAlong (levelAlphaC k M s hM) ha (Finsupp.single x 1)) := by
  intro _ _ hα hβ ha hb x
  exact RibetUsWs.main M s hs hsM p hp hM hS σ hσ hα hβ ha hb x

end S_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
end P2MW
export P2MW.S_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong (solution)
