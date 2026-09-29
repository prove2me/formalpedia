-- Prove2me | solution 1 for Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d6e70ab9-b821-5495-bbea-997596b1d9f8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom

set_option autoImplicit false

namespace C3ESChar

open scoped TensorProduct
open TensorProduct

section LinAlg

variable {F : Type*} [Field F]

theorem coe_restrict_pow {M : Type*} [AddCommGroup M] [Module F M] (f : M →ₗ[F] M)
    (P : Submodule F M) (h : ∀ v ∈ P, f v ∈ P) (k : ℕ) (v : ↥P) :
    (((f.restrict h) ^ k) v : M) = (f ^ k) (v : M) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

theorem exists_common_ker_of_nilpotent : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → (∀ i, IsNilpotent (T i)) → Nontrivial M →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT hnil hM hd
  by_cases hz : ∀ i, T i = 0
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact ⟨v, hv, fun i => by rw [hz i, LinearMap.zero_apply]⟩
  push_neg at hz
  obtain ⟨i₀, hi₀⟩ := hz
  set P : Submodule F M := LinearMap.ker (T i₀) with hP
  have hPtop : P ≠ ⊤ := fun h => hi₀ (LinearMap.ker_eq_top.mp h)
  have hPbot : P ≠ ⊥ := by
    intro h
    have hinj : Function.Injective (T i₀) := LinearMap.ker_eq_bot.mp h
    obtain ⟨k, hk⟩ := hnil i₀
    have hinjk : Function.Injective ((T i₀) ^ k) := by
      rw [Module.End.coe_pow]; exact Function.Injective.iterate hinj k
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact hv (hinjk (by rw [hk, map_zero, LinearMap.zero_apply]))
  have hstab : ∀ i, ∀ v ∈ P, T i v ∈ P := by
    intro i v hv
    rw [hP, LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, (hT i₀ i).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P →ₗ[F] ↥P := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hnil' : ∀ i, IsNilpotent (T' i) := by
    intro i
    obtain ⟨k, hk⟩ := hnil i
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    change ((((T i).restrict (hstab i)) ^ k) v : M) = ((0 : ↥P →ₗ[F] ↥P) v : M)
    rw [coe_restrict_pow, hk]
    rfl
  haveI : Nontrivial ↥P := Submodule.nontrivial_iff_ne_bot.mpr hPbot
  have hlt : Module.finrank F ↥P < d := hd ▸ Submodule.finrank_lt hPtop
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' hnil' inferInstance rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

theorem exists_common_ker_of_range_le : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → ∀ (P : Submodule F M), P ≠ ⊤ → (∀ i x, T i x ∈ P) →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT P hP hTP hd
  by_cases hall : ∀ i, IsNilpotent (T i)
  ·
    have hex : ∃ v : M, v ∉ P := by
      by_contra h
      push_neg at h
      exact hP (Submodule.eq_top_iff'.mpr h)
    obtain ⟨v, hv⟩ := hex
    have hv0 : v ≠ 0 := fun h => hv (h ▸ P.zero_mem)
    haveI : Nontrivial M := nontrivial_of_ne v 0 hv0
    exact exists_common_ker_of_nilpotent d T hT hall inferInstance hd
  push_neg at hall
  obtain ⟨i₀, hi₀⟩ := hall
  set f := T i₀ with hf

  obtain ⟨k, hk, hk1⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow f).and (Filter.eventually_ge_atTop 1)).exists
  set P' : Submodule F M := LinearMap.ker (f ^ k) with hP'
  set Q : Submodule F M := LinearMap.range (f ^ k) with hQ
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hi₀
    exact ⟨k, LinearMap.range_eq_bot.mp h⟩
  have hP'top : P' ≠ ⊤ := by
    intro h
    have hdis := hk.disjoint
    rw [h] at hdis
    exact hQbot (top_disjoint.mp hdis)

  have hQP : Q ≤ P := by
    rintro _ ⟨x, rfl⟩
    have hfk : f ^ k = f * f ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk1]
    rw [hfk, Module.End.mul_apply]
    exact hTP i₀ _

  have hP'P : P.comap P'.subtype ≠ ⊤ := by
    intro h
    have hle : P' ≤ P := fun v hv => by
      have : (⟨v, hv⟩ : ↥P') ∈ P.comap P'.subtype := by rw [h]; trivial
      exact this
    apply hP
    rw [eq_top_iff, ← hk.codisjoint.eq_top]
    exact sup_le hle hQP

  have hstab : ∀ i, ∀ v ∈ P', T i v ∈ P' := by
    intro i v hv
    rw [hP', LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, ((hT i₀ i).pow_left k).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P' →ₗ[F] ↥P' := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hTP' : ∀ i (x : ↥P'), T' i x ∈ P.comap P'.subtype := fun i x => hTP i (x : M)
  have hlt : Module.finrank F ↥P' < d := hd ▸ Submodule.finrank_lt hP'top
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' (P.comap P'.subtype) hP'P hTP' rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

theorem exists_common_eigenvector {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    {ι : Type*} (T : ι → M →ₗ[F] M) (hT : ∀ i j, Commute (T i) (T j)) (c : ι → F)
    (P : Submodule F M) (hP : P ≠ ⊤) (hTP : ∀ i x, T i x - c i • x ∈ P) :
    ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = c i • v := by
  let T' : ι → M →ₗ[F] M := fun i => T i - c i • 1
  have hT' : ∀ i j, Commute (T' i) (T' j) := by
    intro i j
    refine Commute.sub_left (Commute.sub_right (hT i j) ?_) (Commute.sub_right ?_ ?_)
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.refl (1 : M →ₗ[F] M)).smul_right _).smul_left _
  have hTP' : ∀ i x, T' i x ∈ P := fun i x => by
    simpa [T', LinearMap.sub_apply, LinearMap.smul_apply] using hTP i x
  obtain ⟨v, hv, hTv⟩ := exists_common_ker_of_range_le _ T' hT' P hP hTP' rfl
  refine ⟨v, hv, fun i => ?_⟩
  have := hTv i
  simp only [T', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

end LinAlg

section Support

theorem nontrivial_tensorProduct_of_faithfulSMul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] [FaithfulSMul A M] {F : Type*} [Field F] [Algebra A F] :
    Nontrivial (F ⊗[A] M) := by
  let p : PrimeSpectrum A := ⟨RingHom.ker (algebraMap A F), RingHom.ker_isPrime _⟩
  haveI : p.asIdeal.IsPrime := p.2
  have hsupp : p ∈ Module.support A M := by
    rw [Module.mem_support_iff_of_finite,
      (Module.annihilator_eq_bot (R := A) (M := M)).mpr inferInstance]
    exact bot_le
  haveI hnt : Nontrivial (p.asIdeal.ResidueField ⊗[A] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp hsupp

  have hunit : p.asIdeal.primeCompl ≤ (IsUnit.submonoid F).comap (algebraMap A F) := by
    intro a ha
    change IsUnit (algebraMap A F a)
    exact isUnit_iff_ne_zero.mpr ha
  letI : Algebra p.asIdeal.ResidueField F :=
    (Ideal.ResidueField.lift p.asIdeal (algebraMap A F) le_rfl hunit).toAlgebra
  haveI : IsScalarTower A p.asIdeal.ResidueField F := IsScalarTower.of_algebraMap_eq fun a =>
    (Ideal.ResidueField.lift_algebraMap p.asIdeal (algebraMap A F) le_rfl hunit a).symm
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField F F M
  obtain ⟨⟨I, b⟩⟩ :=
    (inferInstance : Module.Free p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M))
  haveI : Nonempty I := b.index_nonempty
  let B := Algebra.TensorProduct.basis F b
  have hB : B (Classical.arbitrary I) ≠ 0 := B.ne_zero _
  exact ⟨⟨e (B (Classical.arbitrary I)), 0, by simpa using hB⟩⟩

end Support

section Main

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  {F : Type*} [Field F] [Algebra R F] {ι : Type*}

open scoped IsMulCommutative in

theorem main' (t : ι → Module.End R M) (A : Subalgebra R (Module.End R M)) [IsMulCommutative ↥A]
    (htA : ∀ i, t i ∈ A) (χ : ↥A →ₐ[R] F) :
    ∃ y : F ⊗[R] M, y ≠ 0 ∧ ∀ i, (t i).baseChange F y = χ ⟨t i, htA i⟩ • y := by
  letI : CommRing ↥A := inferInstance
  haveI : Module.Finite (↥A) M := Module.Finite.of_restrictScalars_finite R (↥A) M
  letI : Algebra (↥A) F := (χ : ↥A →+* F).toAlgebra
  haveI : IsScalarTower R (↥A) F := IsScalarTower.of_algebraMap_eq fun r => (χ.commutes r).symm
  haveI : Nontrivial (F ⊗[↥A] M) := nontrivial_tensorProduct_of_faithfulSMul

  let π : F ⊗[R] M →ₗ[F] F ⊗[↥A] M := TensorProduct.mapOfCompatibleSMul (↥A) R F F M
  have hπ : Function.Surjective π := TensorProduct.mapOfCompatibleSMul_surjective (↥A) R F F M
  have key : ∀ (a : ↥A) (c : F) (m : M), (a • c) ⊗ₜ[↥A] m = c ⊗ₜ[↥A] (a • m) := fun a c m =>
    Quotient.sound' <| AddConGen.Rel.of _ _ <| TensorProduct.Eqv.of_smul _ _ _
  have hπt : ∀ i y, π ((t i).baseChange F y) = χ ⟨t i, htA i⟩ • π y := by
    intro i y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul c m =>
      rw [LinearMap.baseChange_tmul]
      change c ⊗ₜ[↥A] ((⟨t i, htA i⟩ : ↥A) • m) = χ ⟨t i, htA i⟩ • (c ⊗ₜ[↥A] m)
      rw [← key, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
      rfl

  haveI : Module.Finite F (F ⊗[R] M) := Module.Finite.base_change R F M
  have hP : LinearMap.ker π ≠ ⊤ := by
    intro h
    obtain ⟨q, hq⟩ := exists_ne (0 : F ⊗[↥A] M)
    obtain ⟨y, rfl⟩ := hπ q
    have : y ∈ LinearMap.ker π := by rw [h]; trivial
    exact hq (LinearMap.mem_ker.mp this)
  have hcomm : ∀ i j, Commute ((t i).baseChange F) ((t j).baseChange F) := by
    intro i j
    have hij : t i * t j = t j * t i :=
      Subtype.ext_iff.mp (mul_comm (⟨t i, htA i⟩ : ↥A) (⟨t j, htA j⟩ : ↥A))
    change (t i).baseChange F * (t j).baseChange F = (t j).baseChange F * (t i).baseChange F
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hij]
  exact exists_common_eigenvector (fun i => (t i).baseChange F) hcomm (fun i => χ ⟨t i, htA i⟩)
    (LinearMap.ker π) hP (fun i y => by rw [LinearMap.mem_ker, map_sub, map_smul, hπt, sub_self])

theorem main (t : ι → Module.End R M) (ht : ∀ i j, Commute (t i) (t j))
    (χ : ↥(Algebra.adjoin R (Set.range t)) →ₐ[R] F) :
    ∃ y : F ⊗[R] M, y ≠ 0 ∧
      ∀ i, (t i).baseChange F y = χ ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ • y :=
  haveI : IsMulCommutative ↥(Algebra.adjoin R (Set.range t)) := Algebra.isMulCommutative_adjoin R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact (ht i j).eq)
  main' t _ (fun i => Algebra.subset_adjoin (Set.mem_range_self i)) χ

end Main

end C3ESChar

open scoped TensorProduct in

theorem solution
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {F : Type*} [Field F] [Algebra R F]
    {ι : Type*} (t : ι → Module.End R M) (ht : ∀ i j, Commute (t i) (t j))
    (χ : ↥(Algebra.adjoin R (Set.range t)) →ₐ[R] F) :
    ∃ y : F ⊗[R] M, y ≠ 0 ∧
      ∀ i, (t i).baseChange F y = χ ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ • y :=
  C3ESChar.main t ht χ

end S_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom
end P2MW
export P2MW.S_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom (solution)
