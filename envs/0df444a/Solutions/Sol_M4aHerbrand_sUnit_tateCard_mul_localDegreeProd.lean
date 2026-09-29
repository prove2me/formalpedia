-- Prove2me | solution 1 for M4aHerbrand.sUnit_tateCard_mul_localDegreeProd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5f63dcee-f945-59ce-9c1a-62af81703c0c

import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Ring.Aut
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorems.Thm_M4aHerbrand_sUnitQuot_fixedRank_eq
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

section Fold_CyclicRationalClassification

open Polynomial

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace CyclicRational
p2m_open "M4aHerbrand"

universe u v

section OnePiece

variable {M : Type u} {N : Type v}
  [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M]
  [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N] [IsScalarTower ℚ ℚ[X] N]

theorem finite_rat_torsionBy [Module.Finite ℚ M] (p : ℚ[X]) :
    Module.Finite ℚ (Submodule.torsionBy ℚ[X] M p) :=
  Module.Finite.of_injective ((Submodule.torsionBy ℚ[X] M p).subtype.restrictScalars ℚ)
    Subtype.val_injective

scoped instance isScalarTower_quot_torsionBy (p : ℚ[X]) {S : Type*} [SMul S ℚ[X]] [SMul S M]
    [IsScalarTower S ℚ[X] M] [IsScalarTower S ℚ[X] ℚ[X]] :
    IsScalarTower S (ℚ[X] ⧸ Ideal.span {p}) (Submodule.torsionBy ℚ[X] M p) :=
  ⟨fun b d x => Quotient.inductionOn' d fun c => (smul_assoc b c x :)⟩

theorem nonempty_linearEquiv_torsionBy_of_irreducible [Module.Finite ℚ M] [Module.Finite ℚ N]
    {p : ℚ[X]} (hp : Irreducible p)
    (h : Module.finrank ℚ (Submodule.torsionBy ℚ[X] M p)
      = Module.finrank ℚ (Submodule.torsionBy ℚ[X] N p)) :
    Nonempty (Submodule.torsionBy ℚ[X] M p ≃ₗ[ℚ[X]] Submodule.torsionBy ℚ[X] N p) := by
  haveI hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  letI : Field (ℚ[X] ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  haveI : Module.Finite ℚ (ℚ[X] ⧸ Ideal.span {p}) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  haveI := finite_rat_torsionBy (M := M) p
  haveI := finite_rat_torsionBy (M := N) p
  haveI : Module.Finite (ℚ[X] ⧸ Ideal.span {p}) (Submodule.torsionBy ℚ[X] M p) :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : Module.Finite (ℚ[X] ⧸ Ideal.span {p}) (Submodule.torsionBy ℚ[X] N p) :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  have hK : 0 < Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {p}) := Module.finrank_pos
  have hM := Module.finrank_mul_finrank ℚ (ℚ[X] ⧸ Ideal.span {p}) (Submodule.torsionBy ℚ[X] M p)
  have hN := Module.finrank_mul_finrank ℚ (ℚ[X] ⧸ Ideal.span {p}) (Submodule.torsionBy ℚ[X] N p)
  have hdim : Module.finrank (ℚ[X] ⧸ Ideal.span {p}) (Submodule.torsionBy ℚ[X] M p)
      = Module.finrank (ℚ[X] ⧸ Ideal.span {p}) (Submodule.torsionBy ℚ[X] N p) :=
    Nat.eq_of_mul_eq_mul_left hK (hM.trans (h.trans hN.symm))
  exact ⟨(LinearEquiv.ofFinrankEq _ _ hdim).restrictScalars ℚ[X]⟩

end OnePiece

section Classification

variable {M : Type u} {N : Type v}
  [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M]
  [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N] [IsScalarTower ℚ ℚ[X] N]

theorem pairwise_isCoprime_cyclotomic (n : ℕ) :
    ((n.divisors : Finset ℕ) : Set ℕ).Pairwise fun i j => IsCoprime (cyclotomic i ℚ) (cyclotomic j ℚ) :=
  fun _ _ _ _ hij => cyclotomic.isCoprime_rat hij

omit [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] in

theorem isInternal_torsionBy_cyclotomic {n : ℕ} (hn : 0 < n)
    (hM : Module.IsTorsionBy ℚ[X] M (X ^ n - 1)) :
    DirectSum.IsInternal fun d : (n.divisors : Finset ℕ) =>
      Submodule.torsionBy ℚ[X] M (cyclotomic (d : ℕ) ℚ) := by
  have hM' : Module.IsTorsionBy ℚ[X] M (∏ i ∈ n.divisors, cyclotomic i ℚ) := by
    rw [prod_cyclotomic_eq_X_pow_sub_one hn]
    exact hM
  exact Submodule.torsionBy_isInternal (ι := ℕ) (S := n.divisors) (q := fun d => cyclotomic d ℚ)
    (pairwise_isCoprime_cyclotomic n) hM'

theorem nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
    [Module.Finite ℚ M] [Module.Finite ℚ N] {n : ℕ} (hn : 0 < n)
    (hM : Module.IsTorsionBy ℚ[X] M (X ^ n - 1)) (hN : Module.IsTorsionBy ℚ[X] N (X ^ n - 1))
    (h : ∀ d ∈ n.divisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ))
      = Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ))) :
    Nonempty (M ≃ₗ[ℚ[X]] N) := by
  classical
  have e : ∀ d : (n.divisors : Finset ℕ),
      Submodule.torsionBy ℚ[X] M (cyclotomic (d : ℕ) ℚ)
        ≃ₗ[ℚ[X]] Submodule.torsionBy ℚ[X] N (cyclotomic (d : ℕ) ℚ) :=
    fun d => Classical.choice (nonempty_linearEquiv_torsionBy_of_irreducible
      (cyclotomic.irreducible_rat (Nat.pos_of_mem_divisors d.2)) (h d d.2))
  let eM := LinearEquiv.ofBijective (DirectSum.coeLinearMap fun d : (n.divisors : Finset ℕ) =>
    Submodule.torsionBy ℚ[X] M (cyclotomic (d : ℕ) ℚ)) (isInternal_torsionBy_cyclotomic hn hM)
  let eN := LinearEquiv.ofBijective (DirectSum.coeLinearMap fun d : (n.divisors : Finset ℕ) =>
    Submodule.torsionBy ℚ[X] N (cyclotomic (d : ℕ) ℚ)) (isInternal_torsionBy_cyclotomic hn hN)
  let eMid := LinearEquiv.ofBijective (DirectSum.lmap fun d => (e d).toLinearMap)
    ⟨(DirectSum.lmap_injective _).2 fun d => (e d).injective,
      (DirectSum.lmap_surjective _).2 fun d => (e d).surjective⟩
  exact ⟨eM.symm.trans (eMid.trans eN)⟩

end Classification

end M4aHerbrand.CyclicRational
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand"

end Fold_CyclicRationalClassification
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"

section Fold_CyclicRationalFixedRanks

open Polynomial

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace CyclicRational
p2m_open "M4aHerbrand"

universe u v

variable {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M]

omit [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] in

theorem cyclotomic_dvd_X_pow_sub_one_of_dvd {d e : ℕ} (he : 0 < e) (hd : d ∣ e) :
    cyclotomic d ℚ ∣ (X ^ e - 1 : ℚ[X]) := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one he ℚ]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors.2 ⟨hd, he.ne'⟩)

omit [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] in

noncomputable def torsionByTorsionByEquiv {d e : ℕ} (he : 0 < e) (hd : d ∣ e) :
    Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])) (cyclotomic d ℚ)
      ≃ₗ[ℚ[X]] Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ) where
  toFun x := ⟨(x : Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])), by
    have hx := x.2
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    exact congrArg Subtype.val hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨⟨(m : M), by
    obtain ⟨q, hq⟩ := cyclotomic_dvd_X_pow_sub_one_of_dvd he hd
    have hm := m.2
    rw [Submodule.mem_torsionBy_iff] at hm ⊢
    rw [hq, mul_comm, mul_smul, hm, smul_zero]⟩, by
    have hm := m.2
    rw [Submodule.mem_torsionBy_iff] at hm ⊢
    exact Subtype.ext hm⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxSynthPendingDepth 3 in

theorem finrank_torsionBy_X_pow_sub_one [Module.Finite ℚ M] {e : ℕ} (he : 0 < e) :
    Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X]))
      = ∑ d ∈ e.divisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) := by
  classical
  have hMe : Module.IsTorsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])) (X ^ e - 1 : ℚ[X]) :=
    Submodule.torsionBy_isTorsionBy _
  haveI : Module.Finite ℚ (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])) := finite_rat_torsionBy _
  haveI : ∀ d : (e.divisors : Finset ℕ), Module.Finite ℚ
      (Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])) (cyclotomic (d : ℕ) ℚ)) :=
    fun _ => finite_rat_torsionBy _
  haveI : ∀ d : (e.divisors : Finset ℕ), Module.Free ℚ
      (Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])) (cyclotomic (d : ℕ) ℚ)) :=
    fun d => Module.Free.of_divisionRing ℚ
      (Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])) (cyclotomic (d : ℕ) ℚ))
  have eInt := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun d : (e.divisors : Finset ℕ) =>
    Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])) (cyclotomic (d : ℕ) ℚ))
    (isInternal_torsionBy_cyclotomic he hMe)).restrictScalars ℚ
  rw [← eInt.finrank_eq, Module.finrank_directSum]
  have hpiece : ∀ d : (e.divisors : Finset ℕ), Module.finrank ℚ
      (Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X])) (cyclotomic (d : ℕ) ℚ))
        = Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic (d : ℕ) ℚ)) :=
    fun d => ((torsionByTorsionByEquiv (M := M) he (Nat.dvd_of_mem_divisors d.2)).restrictScalars ℚ).finrank_eq
  rw [Finset.sum_congr rfl fun d _ => hpiece d]
  exact Finset.sum_coe_sort e.divisors
    (fun d => Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)))

variable {N : Type v} [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N] [IsScalarTower ℚ ℚ[X] N]

theorem finrank_torsionBy_cyclotomic_eq_of_fixedRanks [Module.Finite ℚ M] [Module.Finite ℚ N] {n : ℕ}
    (hn : 0 < n)
    (h : ∀ e ∈ n.divisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X]))
      = Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (X ^ e - 1 : ℚ[X]))) :
    ∀ d ∈ n.divisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ))
      = Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have key := h d hd
    rw [finrank_torsionBy_X_pow_sub_one hd0, finrank_torsionBy_X_pow_sub_one hd0,
      ← Nat.cons_self_properDivisors hd0.ne', Finset.sum_cons, Finset.sum_cons] at key
    have hrest : ∑ x ∈ d.properDivisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic x ℚ))
        = ∑ x ∈ d.properDivisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic x ℚ)) :=
      Finset.sum_congr rfl fun x hx => ih x (Nat.mem_properDivisors.1 hx).2
        (Nat.mem_divisors.2 ⟨(Nat.mem_properDivisors.1 hx).1.trans hdn, hn.ne'⟩)
    rw [hrest] at key
    exact Nat.add_right_cancel key

theorem nonempty_linearEquiv_of_fixedRanks [Module.Finite ℚ M] [Module.Finite ℚ N] {n : ℕ} (hn : 0 < n)
    (hM : Module.IsTorsionBy ℚ[X] M (X ^ n - 1 : ℚ[X])) (hN : Module.IsTorsionBy ℚ[X] N (X ^ n - 1 : ℚ[X]))
    (h : ∀ e ∈ n.divisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (X ^ e - 1 : ℚ[X]))
      = Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (X ^ e - 1 : ℚ[X]))) :
    Nonempty (M ≃ₗ[ℚ[X]] N) :=
  nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq hn hM hN
    (finrank_torsionBy_cyclotomic_eq_of_fixedRanks hn h)

end M4aHerbrand.CyclicRational
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"

end Fold_CyclicRationalFixedRanks
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"

section Fold_CyclicRationalEndomorphism

open Polynomial

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace CyclicRational
p2m_open "M4aHerbrand"

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

set_option backward.isDefEq.respectTransparency false in

noncomputable def kerAEvalEquivTorsionBy (σ : V →ₗ[ℚ] V) (p : ℚ[X]) :
    LinearMap.ker (aeval σ p) ≃ₗ[ℚ] Submodule.torsionBy ℚ[X] (Module.AEval' σ) p where
  toFun v := ⟨Module.AEval'.of σ (v : V), by
    have hv := v.2
    rw [LinearMap.mem_ker] at hv
    rw [Submodule.mem_torsionBy_iff, ← Module.AEval.of_aeval_smul, Module.End.smul_def, hv, map_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨(Module.AEval'.of σ).symm (m : Module.AEval' σ), by
    have hm := m.2
    rw [Submodule.mem_torsionBy_iff] at hm
    have h' := congrArg (Module.AEval'.of σ).symm hm
    rw [Module.AEval.of_symm_smul, map_zero] at h'
    rw [LinearMap.mem_ker]
    exact h'⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option backward.isDefEq.respectTransparency false in

theorem isTorsionBy_aeval_of_pow_eq_one (σ : V →ₗ[ℚ] V) {n : ℕ} (hσ : σ ^ n = 1) :
    Module.IsTorsionBy ℚ[X] (Module.AEval' σ) (X ^ n - 1 : ℚ[X]) := by
  intro m
  obtain ⟨v, rfl⟩ : ∃ v, Module.AEval'.of σ v = m :=
    ⟨(Module.AEval'.of σ).symm m, (Module.AEval'.of σ).apply_symm_apply m⟩
  show (X ^ n - 1 : ℚ[X]) • Module.AEval.of ℚ V σ v = 0
  rw [← Module.AEval.of_aeval_smul, map_sub, aeval_X_pow, map_one, hσ, sub_self, zero_smul, map_zero]

set_option backward.isDefEq.respectTransparency false in

theorem aeval_X_pow_sub_one (σ : V →ₗ[ℚ] V) (e : ℕ) :
    aeval σ (X ^ e - 1 : ℚ[X]) = σ ^ e - 1 := by
  rw [map_sub, aeval_X_pow, map_one]

variable {W : Type v} [AddCommGroup W] [Module ℚ W]

set_option backward.isDefEq.respectTransparency false in

theorem exists_linearEquiv_intertwining_of_fixedRanks [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]
    (σ : V →ₗ[ℚ] V) (τ : W →ₗ[ℚ] W) {n : ℕ} (hn : 0 < n) (hσ : σ ^ n = 1) (hτ : τ ^ n = 1)
    (h : ∀ e ∈ n.divisors, Module.finrank ℚ (LinearMap.ker (σ ^ e - 1))
      = Module.finrank ℚ (LinearMap.ker (τ ^ e - 1))) :
    ∃ f : V ≃ₗ[ℚ] W, ∀ v, f (σ v) = τ (f v) := by
  have hM := isTorsionBy_aeval_of_pow_eq_one σ hσ
  have hN := isTorsionBy_aeval_of_pow_eq_one τ hτ
  have h' : ∀ e ∈ n.divisors,
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] (Module.AEval' σ) (X ^ e - 1 : ℚ[X]))
        = Module.finrank ℚ (Submodule.torsionBy ℚ[X] (Module.AEval' τ) (X ^ e - 1 : ℚ[X])) := by
    intro e he
    rw [← (kerAEvalEquivTorsionBy σ (X ^ e - 1 : ℚ[X])).finrank_eq,
      ← (kerAEvalEquivTorsionBy τ (X ^ e - 1 : ℚ[X])).finrank_eq,
      aeval_X_pow_sub_one, aeval_X_pow_sub_one]
    exact h e he
  obtain ⟨g⟩ := nonempty_linearEquiv_of_fixedRanks (M := Module.AEval' σ) (N := Module.AEval' τ)
    hn hM hN h'
  refine ⟨(Module.AEval'.of σ).trans ((g.restrictScalars ℚ).trans (Module.AEval'.of τ).symm), fun v => ?_⟩
  show (Module.AEval'.of τ).symm (g (Module.AEval'.of σ (σ v)))
    = τ ((Module.AEval'.of τ).symm (g (Module.AEval'.of σ v)))
  rw [← Module.AEval'.X_smul_of, LinearEquiv.map_smul, Module.AEval'.of_symm_X_smul]

end M4aHerbrand.CyclicRational
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"

end Fold_CyclicRationalEndomorphism
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"

section Fold_HerbrandQuotient

open Finset

namespace M4aLocalCFT

universe u

variable {A : Type u} [AddCommGroup A]

structure HerbrandPair (A : Type u) [AddCommGroup A] where

  derive : A →+ A

  norm : A →+ A

  derive_norm : ∀ a : A, derive (norm a) = 0

  norm_derive : ∀ a : A, norm (derive a) = 0

namespace HerbrandPair

variable (P : HerbrandPair A)

theorem range_norm_le_ker_derive : P.norm.range ≤ P.derive.ker := by
  rintro b ⟨a, rfl⟩
  exact P.derive_norm a

theorem range_derive_le_ker_norm : P.derive.range ≤ P.norm.ker := by
  rintro b ⟨a, rfl⟩
  exact P.norm_derive a

noncomputable def tateCard₀ : ℕ :=
  Nat.card (P.derive.ker ⧸ P.norm.range.addSubgroupOf P.derive.ker)

noncomputable def tateCard₁ : ℕ :=
  Nat.card (P.norm.ker ⧸ P.derive.range.addSubgroupOf P.norm.ker)

section Lagrange

private theorem card_ker_derive_eq :
    Nat.card P.derive.ker = P.tateCard₀ * Nat.card P.norm.range := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (P.norm.range.addSubgroupOf P.derive.ker)
  rw [h]
  congr 1
  exact Nat.card_congr
    (AddSubgroup.addSubgroupOfEquivOfLe P.range_norm_le_ker_derive).toEquiv

private theorem card_ker_norm_eq :
    Nat.card P.norm.ker = P.tateCard₁ * Nat.card P.derive.range := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (P.derive.range.addSubgroupOf P.norm.ker)
  rw [h]
  congr 1
  exact Nat.card_congr
    (AddSubgroup.addSubgroupOfEquivOfLe P.range_derive_le_ker_norm).toEquiv

private theorem card_eq_card_range_mul_card_ker (f : A →+ A) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker]
  congr 1
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv

end Lagrange
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"

theorem tateCard₀_eq_tateCard₁_of_finite [Finite A] : P.tateCard₀ = P.tateCard₁ := by
  haveI : Nonempty P.derive.range := ⟨0⟩
  haveI : Nonempty P.norm.range := ⟨0⟩
  have hDr : 0 < Nat.card P.derive.range := Nat.card_pos
  have hNr : 0 < Nat.card P.norm.range := Nat.card_pos

  have key : Nat.card P.derive.range * Nat.card P.norm.range * P.tateCard₀ =
      Nat.card P.derive.range * Nat.card P.norm.range * P.tateCard₁ := by
    calc Nat.card P.derive.range * Nat.card P.norm.range * P.tateCard₀
        = Nat.card P.derive.range * (P.tateCard₀ * Nat.card P.norm.range) := by ring
      _ = Nat.card P.derive.range * Nat.card P.derive.ker := by rw [← P.card_ker_derive_eq]
      _ = Nat.card A := (card_eq_card_range_mul_card_ker P.derive).symm
      _ = Nat.card P.norm.range * Nat.card P.norm.ker :=
          card_eq_card_range_mul_card_ker P.norm
      _ = Nat.card P.norm.range * (P.tateCard₁ * Nat.card P.derive.range) := by
          rw [← P.card_ker_norm_eq]
      _ = Nat.card P.derive.range * Nat.card P.norm.range * P.tateCard₁ := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hDr hNr) key

theorem tateCard₁_ne_zero_of_finite [Finite A] : P.tateCard₁ ≠ 0 := by
  rw [tateCard₁]
  exact Nat.card_ne_zero.mpr ⟨⟨QuotientAddGroup.mk 0⟩, inferInstance⟩

section Cyclic

variable (σ : AddAut A) (n : ℕ)

private theorem telescope (a : A) :
    ∑ i ∈ range n, ((σ ^ (i + 1)) a - (σ ^ i) a) = (σ ^ n) a - a := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      abel

noncomputable def ofAddAut (hσ : σ ^ n = 1) : HerbrandPair A where
  derive := σ.toAddMonoidHom - AddMonoidHom.id A
  norm := ∑ i ∈ range n, (σ ^ i).toAddMonoidHom
  derive_norm a := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      AddMonoidHom.finsetSum_apply, AddEquiv.coe_toAddMonoidHom]
    rw [map_sum, ← Finset.sum_sub_distrib]
    have hstep : ∀ i ∈ range n, σ ((σ ^ i) a) - (σ ^ i) a
        = (σ ^ (i + 1)) a - (σ ^ i) a := by
      intro i _
      rw [pow_succ', AddAut.mul_apply']
    rw [Finset.sum_congr rfl hstep, telescope σ n a, hσ]
    simp
  norm_derive a := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      AddMonoidHom.finsetSum_apply, AddEquiv.coe_toAddMonoidHom]
    have hstep : ∀ i ∈ range n, (σ ^ i) (σ a - a) = (σ ^ (i + 1)) a - (σ ^ i) a := by
      intro i _
      rw [map_sub, pow_succ, AddAut.mul_apply']
    rw [Finset.sum_congr rfl hstep, telescope σ n a, hσ]
    simp

@[scoped simp] theorem ofAddAut_derive_apply (hσ : σ ^ n = 1) (a : A) :
    (ofAddAut σ n hσ).derive a = σ a - a := rfl

theorem ofAddAut_norm_apply (hσ : σ ^ n = 1) (a : A) :
    (ofAddAut σ n hσ).norm a = ∑ i ∈ range n, (σ ^ i) a := by
  show (∑ i ∈ range n, (σ ^ i).toAddMonoidHom) a = _
  simp only [AddMonoidHom.finsetSum_apply, AddEquiv.coe_toAddMonoidHom]

end Cyclic
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational"

end HerbrandPair
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair"

section Gates

open HerbrandPair

noncomputable def intTrivialPair : HerbrandPair ℤ :=
  ofAddAut (1 : AddAut ℤ) 2 (one_pow 2)

theorem intTrivialPair_norm_apply (a : ℤ) : intTrivialPair.norm a = 2 * a := by
  show (ofAddAut (1 : AddAut ℤ) 2 (one_pow 2)).norm a = 2 * a
  rw [ofAddAut_norm_apply]
  simp [two_mul]

theorem intTrivialPair_derive_apply (a : ℤ) : intTrivialPair.derive a = 0 := by
  show (ofAddAut (1 : AddAut ℤ) 2 (one_pow 2)).derive a = 0
  rw [ofAddAut_derive_apply]
  simp

theorem tateCard₁_intTrivialPair : intTrivialPair.tateCard₁ = 1 := by
  rw [tateCard₁, Nat.card_eq_one_iff_exists]
  have hker : ∀ x : intTrivialPair.norm.ker, x = 0 := by
    rintro ⟨x, hx⟩
    rw [AddMonoidHom.mem_ker, intTrivialPair_norm_apply] at hx
    have : x = 0 := by omega
    exact Subtype.ext this
  exact ⟨QuotientAddGroup.mk 0, fun y =>
    QuotientAddGroup.induction_on y fun x => congrArg QuotientAddGroup.mk (hker x)⟩

theorem tateCard₀_intTrivialPair_ne_one : intTrivialPair.tateCard₀ ≠ 1 := by
  intro h
  rw [tateCard₀, Nat.card_eq_one_iff_exists] at h
  obtain ⟨c, hc⟩ := h

  have h0 : (0 : ℤ) ∈ intTrivialPair.derive.ker := zero_mem _
  have h1 : (1 : ℤ) ∈ intTrivialPair.derive.ker := by
    rw [AddMonoidHom.mem_ker, intTrivialPair_derive_apply]
  have heq : (QuotientAddGroup.mk (⟨0, h0⟩ : intTrivialPair.derive.ker) :
      intTrivialPair.derive.ker ⧸ intTrivialPair.norm.range.addSubgroupOf
        intTrivialPair.derive.ker) = QuotientAddGroup.mk ⟨1, h1⟩ :=
    (hc _).trans (hc _).symm
  have hmem := QuotientAddGroup.eq.mp heq
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨a, ha⟩ := hmem
  rw [intTrivialPair_norm_apply] at ha
  have hval : ((-(⟨0, h0⟩ : intTrivialPair.derive.ker) + ⟨1, h1⟩ :
      intTrivialPair.derive.ker) : ℤ) = 1 := by
    simp
  rw [hval] at ha
  omega

theorem tateCard₀_ne_tateCard₁_int :
    intTrivialPair.tateCard₀ ≠ intTrivialPair.tateCard₁ := by
  rw [tateCard₁_intTrivialPair]
  exact tateCard₀_intTrivialPair_ne_one

noncomputable def zmodTwoPair : HerbrandPair (ZMod 2) :=
  ofAddAut (1 : AddAut (ZMod 2)) 2 (one_pow 2)

theorem zmodTwoPair_norm_apply (a : ZMod 2) : zmodTwoPair.norm a = 0 := by
  show (ofAddAut (1 : AddAut (ZMod 2)) 2 (one_pow 2)).norm a = 0
  rw [ofAddAut_norm_apply]
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, one_pow, AddAut.one_apply',
    zero_add]
  rw [← two_mul, h2, zero_mul]

theorem zmodTwoPair_derive_apply (a : ZMod 2) : zmodTwoPair.derive a = 0 := by
  show (ofAddAut (1 : AddAut (ZMod 2)) 2 (one_pow 2)).derive a = 0
  rw [ofAddAut_derive_apply]
  simp

theorem herbrandPair_zmod_two_fires :
    zmodTwoPair.tateCard₀ = zmodTwoPair.tateCard₁ ∧ zmodTwoPair.tateCard₁ ≠ 1 := by
  refine ⟨zmodTwoPair.tateCard₀_eq_tateCard₁_of_finite, ?_⟩
  intro h
  rw [tateCard₁, Nat.card_eq_one_iff_exists] at h
  obtain ⟨c, hc⟩ := h

  have h0 : (0 : ZMod 2) ∈ zmodTwoPair.norm.ker := zero_mem _
  have h1 : (1 : ZMod 2) ∈ zmodTwoPair.norm.ker := by
    rw [AddMonoidHom.mem_ker, zmodTwoPair_norm_apply]
  have heq : (QuotientAddGroup.mk (⟨0, h0⟩ : zmodTwoPair.norm.ker) :
      zmodTwoPair.norm.ker ⧸ zmodTwoPair.derive.range.addSubgroupOf
        zmodTwoPair.norm.ker) = QuotientAddGroup.mk ⟨1, h1⟩ :=
    (hc _).trans (hc _).symm
  have hmem := QuotientAddGroup.eq.mp heq
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨a, ha⟩ := hmem
  rw [zmodTwoPair_derive_apply] at ha
  have hval : ((-(⟨0, h0⟩ : zmodTwoPair.norm.ker) + ⟨1, h1⟩ :
      zmodTwoPair.norm.ker) : ZMod 2) = 1 := by
    simp
  rw [hval] at ha
  exact one_ne_zero ha.symm

def negAddAut (B : Type*) [AddCommGroup B] : AddAut B where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' := neg_add

theorem negAddAut_sq (B : Type*) [AddCommGroup B] : (negAddAut B) ^ 2 = 1 := by
  ext x
  show (negAddAut B) ((negAddAut B) x) = x
  exact neg_neg x

theorem derive_ofAddAut_negAddAut_ne_zero :
    (ofAddAut (negAddAut (ZMod 4)) 2 (negAddAut_sq _)).derive 1 ≠ 0 := by
  rw [ofAddAut_derive_apply]
  decide

end Gates
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT"

end Fold_HerbrandQuotient
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT"

section Fold_HerbrandQuotientMultiplicative

open Finset

namespace M4aLocalCFT

section ExactCycle

theorem nat_card_eq_card_range_mul_card_ker {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : Nat.card G = Nat.card f.range * Nat.card f.ker := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker]
  congr 1
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv

variable {G₀ G₁ G₂ G₃ G₄ G₅ : Type*}
  [AddCommGroup G₀] [AddCommGroup G₁] [AddCommGroup G₂]
  [AddCommGroup G₃] [AddCommGroup G₄] [AddCommGroup G₅]

theorem card_mul_eq_of_exactCycle
    (f₀ : G₀ →+ G₁) (f₁ : G₁ →+ G₂) (f₂ : G₂ →+ G₃)
    (f₃ : G₃ →+ G₄) (f₄ : G₄ →+ G₅) (f₅ : G₅ →+ G₀)
    (h₀ : f₀.range = f₁.ker) (h₁ : f₁.range = f₂.ker) (h₂ : f₂.range = f₃.ker)
    (h₃ : f₃.range = f₄.ker) (h₄ : f₄.range = f₅.ker) (h₅ : f₅.range = f₀.ker) :
    Nat.card G₀ * Nat.card G₂ * Nat.card G₄ =
      Nat.card G₁ * Nat.card G₃ * Nat.card G₅ := by
  have e₀ : Nat.card G₀ = Nat.card f₀.range * Nat.card f₅.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₀, ← h₅]
  have e₁ : Nat.card G₁ = Nat.card f₁.range * Nat.card f₀.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₁, ← h₀]
  have e₂ : Nat.card G₂ = Nat.card f₂.range * Nat.card f₁.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₂, ← h₁]
  have e₃ : Nat.card G₃ = Nat.card f₃.range * Nat.card f₂.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₃, ← h₂]
  have e₄ : Nat.card G₄ = Nat.card f₄.range * Nat.card f₃.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₄, ← h₃]
  have e₅ : Nat.card G₅ = Nat.card f₅.range * Nat.card f₄.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₅, ← h₄]
  rw [e₀, e₁, e₂, e₃, e₄, e₅]
  ring

end ExactCycle
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT"

namespace HerbrandPair

variable {A : Type*} {B : Type*} [AddCommGroup A] [AddCommGroup B]

@[simps derive norm]
noncomputable def prod (P : HerbrandPair A) (Q : HerbrandPair B) : HerbrandPair (A × B) where
  derive := P.derive.prodMap Q.derive
  norm := P.norm.prodMap Q.norm
  derive_norm a := by
    show (P.derive (P.norm a.1), Q.derive (Q.norm a.2)) = 0
    rw [P.derive_norm a.1, Q.derive_norm a.2]
    rfl
  norm_derive a := by
    show (P.norm (P.derive a.1), Q.norm (Q.derive a.2)) = 0
    rw [P.norm_derive a.1, Q.norm_derive a.2]
    rfl

variable (P : HerbrandPair A) (Q : HerbrandPair B)

private theorem fst_mem_ker_of_mem_ker_prod {x : A × B}
    (hx : x ∈ (P.prod Q).derive.ker) : x.1 ∈ P.derive.ker := by
  rw [AddMonoidHom.mem_ker] at hx ⊢
  exact (Prod.ext_iff.mp hx).1

private theorem snd_mem_ker_of_mem_ker_prod {x : A × B}
    (hx : x ∈ (P.prod Q).derive.ker) : x.2 ∈ Q.derive.ker := by
  rw [AddMonoidHom.mem_ker] at hx ⊢
  exact (Prod.ext_iff.mp hx).2

private noncomputable def prodTateCompare :
    ((P.prod Q).derive.ker) →+
      ((P.derive.ker ⧸ P.norm.range.addSubgroupOf P.derive.ker) ×
       (Q.derive.ker ⧸ Q.norm.range.addSubgroupOf Q.derive.ker)) where
  toFun x :=
    (QuotientAddGroup.mk ⟨x.1.1, fst_mem_ker_of_mem_ker_prod P Q x.2⟩,
     QuotientAddGroup.mk ⟨x.1.2, snd_mem_ker_of_mem_ker_prod P Q x.2⟩)
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem prodTateCompare_surjective :
    Function.Surjective (prodTateCompare P Q) := by
  rintro ⟨c₁, c₂⟩
  refine QuotientAddGroup.induction_on c₁ fun a => ?_
  refine QuotientAddGroup.induction_on c₂ fun b => ?_
  refine ⟨⟨(a.1, b.1), ?_⟩, rfl⟩
  rw [AddMonoidHom.mem_ker]
  show (P.derive a.1, Q.derive b.1) = 0
  rw [AddMonoidHom.mem_ker.mp a.2, AddMonoidHom.mem_ker.mp b.2]
  rfl

private theorem ker_prodTateCompare :
    (prodTateCompare P Q).ker =
      (P.prod Q).norm.range.addSubgroupOf (P.prod Q).derive.ker := by
  ext x
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    have h1 : (QuotientAddGroup.mk ⟨x.1.1, fst_mem_ker_of_mem_ker_prod P Q x.2⟩ :
        P.derive.ker ⧸ P.norm.range.addSubgroupOf P.derive.ker) = 0 := congrArg Prod.fst h
    have h2 : (QuotientAddGroup.mk ⟨x.1.2, snd_mem_ker_of_mem_ker_prod P Q x.2⟩ :
        Q.derive.ker ⧸ Q.norm.range.addSubgroupOf Q.derive.ker) = 0 := congrArg Prod.snd h
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1 h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨⟨a, b⟩, hab⟩
    have ha : P.norm a = x.1.1 := congrArg Prod.fst hab
    have hb : Q.norm b = x.1.2 := congrArg Prod.snd hab
    refine Prod.ext ?_ ?_ <;>
      simp only [prodTateCompare, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero,
        Prod.snd_zero] <;>
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩

theorem tateCard₀_prod : (P.prod Q).tateCard₀ = P.tateCard₀ * Q.tateCard₀ := by
  rw [tateCard₀, tateCard₀, tateCard₀, ← Nat.card_prod, ← ker_prodTateCompare]
  exact Nat.card_congr
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (prodTateCompare_surjective P Q)).symm.toEquiv |>.symm

@[simps derive norm]
noncomputable def swap (P : HerbrandPair A) : HerbrandPair A where
  derive := P.norm
  norm := P.derive
  derive_norm := P.norm_derive
  norm_derive := P.derive_norm

@[scoped simp] theorem tateCard₀_swap : P.swap.tateCard₀ = P.tateCard₁ := rfl

@[scoped simp] theorem tateCard₁_swap : P.swap.tateCard₁ = P.tateCard₀ := rfl

@[scoped simp] theorem swap_swap : P.swap.swap = P := rfl

theorem swap_prod : (P.prod Q).swap = P.swap.prod Q.swap := rfl

theorem tateCard₁_prod : (P.prod Q).tateCard₁ = P.tateCard₁ * Q.tateCard₁ := by
  have := tateCard₀_prod P.swap Q.swap
  rwa [← swap_prod, tateCard₀_swap, tateCard₀_swap, tateCard₀_swap] at this

end HerbrandPair
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT"

open HerbrandPair

structure HerbrandTriple (A B C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where

  P : HerbrandPair A

  Q : HerbrandPair B

  R : HerbrandPair C

  ι : A →+ B

  π : B →+ C

  ι_injective : Function.Injective ι

  π_surjective : Function.Surjective π

  exact : ι.range = π.ker

  derive_ι : ∀ a, Q.derive (ι a) = ι (P.derive a)

  norm_ι : ∀ a, Q.norm (ι a) = ι (P.norm a)

  derive_π : ∀ b, R.derive (π b) = π (Q.derive b)

  norm_π : ∀ b, R.norm (π b) = π (Q.norm b)

namespace HerbrandTriple

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable (T : HerbrandTriple A B C)

noncomputable def swap : HerbrandTriple A B C where
  P := T.P.swap
  Q := T.Q.swap
  R := T.R.swap
  ι := T.ι
  π := T.π
  ι_injective := T.ι_injective
  π_surjective := T.π_surjective
  exact := T.exact
  derive_ι := T.norm_ι
  norm_ι := T.derive_ι
  derive_π := T.norm_π
  norm_π := T.derive_π

@[scoped simp] theorem swap_swap : T.swap.swap = T := rfl

theorem exists_of_π_eq_zero {b : B} (hb : T.π b = 0) : ∃ a, T.ι a = b := by
  have : b ∈ T.π.ker := hb
  rw [← T.exact] at this
  exact this

private def ιKer : (T.P.derive.ker : AddSubgroup A) →+ (T.Q.derive.ker : AddSubgroup B) where
  toFun a := ⟨T.ι a.1, by
    rw [AddMonoidHom.mem_ker, T.derive_ι, AddMonoidHom.mem_ker.mp a.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero T.ι)
  map_add' a b := Subtype.ext (map_add T.ι a.1 b.1)

@[scoped simp] private theorem ιKer_coe (a : T.P.derive.ker) : (T.ιKer a : B) = T.ι a.1 := rfl

private def πKer : (T.Q.derive.ker : AddSubgroup B) →+ (T.R.derive.ker : AddSubgroup C) where
  toFun b := ⟨T.π b.1, by
    rw [AddMonoidHom.mem_ker, T.derive_π, AddMonoidHom.mem_ker.mp b.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero T.π)
  map_add' a b := Subtype.ext (map_add T.π a.1 b.1)

@[scoped simp] private theorem πKer_coe (b : T.Q.derive.ker) : (T.πKer b : C) = T.π b.1 := rfl

noncomputable def inducedι :
    (T.P.derive.ker ⧸ T.P.norm.range.addSubgroupOf T.P.derive.ker) →+
      (T.Q.derive.ker ⧸ T.Q.norm.range.addSubgroupOf T.Q.derive.ker) :=
  QuotientAddGroup.map _ _ T.ιKer (by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf] at hx
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    obtain ⟨a, ha⟩ := hx
    exact ⟨T.ι a, by rw [T.norm_ι, ha]; rfl⟩)

noncomputable def inducedπ :
    (T.Q.derive.ker ⧸ T.Q.norm.range.addSubgroupOf T.Q.derive.ker) →+
      (T.R.derive.ker ⧸ T.R.norm.range.addSubgroupOf T.R.derive.ker) :=
  QuotientAddGroup.map _ _ T.πKer (by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf] at hx
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    obtain ⟨b, hb⟩ := hx
    exact ⟨T.π b, by rw [T.norm_π, hb]; rfl⟩)

@[scoped simp] theorem inducedι_mk (a : T.P.derive.ker) :
    T.inducedι (QuotientAddGroup.mk a) = QuotientAddGroup.mk (T.ιKer a) :=
  rfl

@[scoped simp] theorem inducedπ_mk (b : T.Q.derive.ker) :
    T.inducedπ (QuotientAddGroup.mk b) = QuotientAddGroup.mk (T.πKer b) :=
  rfl

def ConnectingRel (c : C) (a : A) : Prop :=
  ∃ b : B, T.π b = c ∧ T.ι a = T.Q.derive b

theorem connectingRel_exists {c : C} (hc : c ∈ T.R.derive.ker) :
    ∃ a, a ∈ T.P.norm.ker ∧ T.ConnectingRel c a := by
  obtain ⟨b, rfl⟩ := T.π_surjective c
  have hdb : T.π (T.Q.derive b) = 0 := by
    rw [← T.derive_π]
    exact AddMonoidHom.mem_ker.mp hc
  obtain ⟨a, ha⟩ := T.exists_of_π_eq_zero hdb
  refine ⟨a, ?_, b, rfl, ha⟩
  rw [AddMonoidHom.mem_ker]
  apply T.ι_injective
  rw [← T.norm_ι, ha, T.Q.norm_derive, map_zero]

theorem connectingRel_sub_mem {c : C} {a a' : A} (h : T.ConnectingRel c a)
    (h' : T.ConnectingRel c a') : a - a' ∈ T.P.derive.range := by
  obtain ⟨b, hb, hab⟩ := h
  obtain ⟨b', hb', hab'⟩ := h'
  have hbb' : T.π (b - b') = 0 := by rw [map_sub, hb, hb', sub_self]
  obtain ⟨x, hx⟩ := T.exists_of_π_eq_zero hbb'
  refine ⟨x, T.ι_injective ?_⟩
  rw [← T.derive_ι, hx, map_sub, map_sub, hab, hab']

theorem connectingRel_add {c c' : C} {a a' : A} (h : T.ConnectingRel c a)
    (h' : T.ConnectingRel c' a') : T.ConnectingRel (c + c') (a + a') := by
  obtain ⟨b, hb, hab⟩ := h
  obtain ⟨b', hb', hab'⟩ := h'
  exact ⟨b + b', by rw [map_add, hb, hb'], by rw [map_add, map_add, hab, hab']⟩

theorem connectingRel_zero_of_mem_range_norm {c : C} (hc : c ∈ T.R.norm.range) :
    T.ConnectingRel c 0 := by
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨b', rfl⟩ := T.π_surjective c'
  exact ⟨T.Q.norm b', by rw [T.norm_π], by rw [map_zero, T.Q.derive_norm]⟩

theorem connectingRel_zero : T.ConnectingRel 0 0 :=
  ⟨0, map_zero _, by rw [map_zero, map_zero]⟩

private noncomputable def connectingAux (c : T.R.derive.ker) : A :=
  (T.connectingRel_exists c.2).choose

private theorem connectingAux_mem (c : T.R.derive.ker) :
    T.connectingAux c ∈ T.P.norm.ker :=
  (T.connectingRel_exists c.2).choose_spec.1

private theorem connectingAux_rel (c : T.R.derive.ker) :
    T.ConnectingRel c.1 (T.connectingAux c) :=
  (T.connectingRel_exists c.2).choose_spec.2

private theorem tate₁_mk_eq_mk {a a' : A} (ha : a ∈ T.P.norm.ker) (ha' : a' ∈ T.P.norm.ker) :
    (QuotientAddGroup.mk ⟨a, ha⟩ :
        T.P.norm.ker ⧸ T.P.derive.range.addSubgroupOf T.P.norm.ker) =
      QuotientAddGroup.mk ⟨a', ha'⟩ ↔ a - a' ∈ T.P.derive.range := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    have := T.P.derive.range.neg_mem h
    simpa [neg_add_rev, sub_eq_add_neg, add_comm] using this
  · intro h
    have := T.P.derive.range.neg_mem h
    simpa [neg_sub, sub_eq_neg_add] using this

private noncomputable def connectingHom :
    (T.R.derive.ker : AddSubgroup C) →+
      (T.P.norm.ker ⧸ T.P.derive.range.addSubgroupOf T.P.norm.ker) where
  toFun c := QuotientAddGroup.mk ⟨T.connectingAux c, T.connectingAux_mem c⟩
  map_zero' := by
    rw [show (0 : (T.P.norm.ker ⧸ T.P.derive.range.addSubgroupOf T.P.norm.ker)) =
      QuotientAddGroup.mk ⟨0, T.P.norm.ker.zero_mem⟩ from rfl]
    rw [tate₁_mk_eq_mk]
    exact T.connectingRel_sub_mem (T.connectingAux_rel 0) T.connectingRel_zero
  map_add' c c' := by
    rw [show (QuotientAddGroup.mk ⟨T.connectingAux c, T.connectingAux_mem c⟩ +
        QuotientAddGroup.mk ⟨T.connectingAux c', T.connectingAux_mem c'⟩ :
        T.P.norm.ker ⧸ T.P.derive.range.addSubgroupOf T.P.norm.ker) =
      QuotientAddGroup.mk ⟨T.connectingAux c + T.connectingAux c',
        T.P.norm.ker.add_mem (T.connectingAux_mem c) (T.connectingAux_mem c')⟩ from rfl]
    rw [tate₁_mk_eq_mk]
    exact T.connectingRel_sub_mem (T.connectingAux_rel (c + c'))
      (T.connectingRel_add (T.connectingAux_rel c) (T.connectingAux_rel c'))

noncomputable def connecting :
    (T.R.derive.ker ⧸ T.R.norm.range.addSubgroupOf T.R.derive.ker) →+
      (T.P.norm.ker ⧸ T.P.derive.range.addSubgroupOf T.P.norm.ker) :=
  QuotientAddGroup.lift _ T.connectingHom (by
    intro c hc
    rw [AddSubgroup.mem_addSubgroupOf] at hc
    show (QuotientAddGroup.mk ⟨T.connectingAux c, T.connectingAux_mem c⟩ :
      T.P.norm.ker ⧸ T.P.derive.range.addSubgroupOf T.P.norm.ker) = 0
    rw [show (0 : (T.P.norm.ker ⧸ T.P.derive.range.addSubgroupOf T.P.norm.ker)) =
      QuotientAddGroup.mk ⟨0, T.P.norm.ker.zero_mem⟩ from rfl]
    rw [tate₁_mk_eq_mk]
    exact T.connectingRel_sub_mem (T.connectingAux_rel c) (T.connectingRel_zero_of_mem_range_norm hc))

@[scoped simp] theorem connecting_mk (c : T.R.derive.ker) :
    T.connecting (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk ⟨T.connectingAux c, T.connectingAux_mem c⟩ :=
  rfl

theorem connecting_mk_eq_of_rel {c : T.R.derive.ker} {a : A} (ha : a ∈ T.P.norm.ker)
    (hrel : T.ConnectingRel c.1 a) :
    T.connecting (QuotientAddGroup.mk c) = QuotientAddGroup.mk ⟨a, ha⟩ := by
  rw [connecting_mk, tate₁_mk_eq_mk]
  exact T.connectingRel_sub_mem (T.connectingAux_rel c) hrel

theorem π_ι (a : A) : T.π (T.ι a) = 0 := by
  have h : T.ι a ∈ T.ι.range := ⟨a, rfl⟩
  rw [T.exact] at h
  exact h

private theorem tateQuot_mk_eq_mk {α : Type*} [AddCommGroup α] {K S : AddSubgroup α}
    (x y : K) :
    (QuotientAddGroup.mk x : K ⧸ S.addSubgroupOf K) = QuotientAddGroup.mk y ↔
      (x : α) - y ∈ S := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    have := S.neg_mem h
    simpa [neg_add_rev, sub_eq_add_neg, add_comm] using this
  · intro h
    have := S.neg_mem h
    simpa [neg_sub, sub_eq_neg_add] using this

private theorem tateQuot_mk_eq_zero {α : Type*} [AddCommGroup α] {K S : AddSubgroup α}
    (x : K) :
    (QuotientAddGroup.mk x : K ⧸ S.addSubgroupOf K) = 0 ↔ (x : α) ∈ S := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

theorem exact_at_middle : T.inducedι.range = T.inducedπ.ker := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    refine QuotientAddGroup.induction_on y fun a => ?_
    rw [AddMonoidHom.mem_ker, inducedι_mk, inducedπ_mk, tateQuot_mk_eq_zero]
    show T.π (T.ι a.1) ∈ T.R.norm.range
    rw [T.π_ι]
    exact zero_mem _
  · intro x hx
    revert hx
    refine QuotientAddGroup.induction_on x fun b => ?_
    intro hb
    rw [AddMonoidHom.mem_ker, inducedπ_mk, tateQuot_mk_eq_zero] at hb
    obtain ⟨c, hc⟩ := hb
    obtain ⟨b', rfl⟩ := T.π_surjective c
    have hsub : T.π (b.1 - T.Q.norm b') = 0 := by
      rw [map_sub, ← T.norm_π, hc]
      show T.π b.1 - (T.πKer b).1 = 0
      rw [πKer_coe, sub_self]
    obtain ⟨a, ha⟩ := T.exists_of_π_eq_zero hsub
    have haker : a ∈ T.P.derive.ker := by
      rw [AddMonoidHom.mem_ker]
      apply T.ι_injective
      rw [← T.derive_ι, ha, map_zero, map_sub, T.Q.derive_norm,
        AddMonoidHom.mem_ker.mp b.2, sub_zero]
    refine ⟨QuotientAddGroup.mk ⟨a, haker⟩, ?_⟩
    rw [inducedι_mk, tateQuot_mk_eq_mk]
    show T.ι a - b.1 ∈ T.Q.norm.range
    rw [ha]
    refine ⟨-b', ?_⟩
    rw [map_neg]
    abel

theorem exact_at_quot : T.inducedπ.range = T.connecting.ker := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    refine QuotientAddGroup.induction_on y fun b => ?_
    rw [AddMonoidHom.mem_ker, inducedπ_mk]
    have hrel : T.ConnectingRel (T.πKer b).1 0 :=
      ⟨b.1, rfl, by rw [map_zero, AddMonoidHom.mem_ker.mp b.2]⟩
    rw [T.connecting_mk_eq_of_rel T.P.norm.ker.zero_mem hrel]
    exact (tateQuot_mk_eq_zero _).mpr (zero_mem _)
  · intro x hx
    revert hx
    refine QuotientAddGroup.induction_on x fun c => ?_
    intro hc
    rw [AddMonoidHom.mem_ker, connecting_mk, tateQuot_mk_eq_zero] at hc
    obtain ⟨x', hx'⟩ := hc
    replace hx' : T.P.derive x' = T.connectingAux c := hx'
    obtain ⟨b, hb, hab⟩ := T.connectingAux_rel c
    have hbker : b - T.ι x' ∈ T.Q.derive.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, ← hab, T.derive_ι, hx', sub_self]
    refine ⟨QuotientAddGroup.mk ⟨b - T.ι x', hbker⟩, ?_⟩
    rw [inducedπ_mk, tateQuot_mk_eq_mk]
    show T.π (b - T.ι x') - c.1 ∈ T.R.norm.range
    rw [map_sub, T.π_ι, sub_zero, hb, sub_self]
    exact zero_mem _

theorem exact_at_sub : T.connecting.range = T.swap.inducedι.ker := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    refine QuotientAddGroup.induction_on y fun c => ?_
    obtain ⟨b, hb, hab⟩ := T.connectingAux_rel c
    show T.swap.inducedι (T.connecting (QuotientAddGroup.mk c)) = 0
    rw [connecting_mk]
    show (QuotientAddGroup.mk (T.swap.ιKer ⟨T.connectingAux c, T.connectingAux_mem c⟩) :
      T.swap.Q.derive.ker ⧸ T.swap.Q.norm.range.addSubgroupOf T.swap.Q.derive.ker) = 0
    rw [tateQuot_mk_eq_zero]
    show T.ι (T.connectingAux c) ∈ T.Q.derive.range
    exact ⟨b, hab.symm⟩
  · intro x hx
    revert hx
    refine QuotientAddGroup.induction_on x fun a => ?_
    intro ha
    have ha' : T.ι a.1 ∈ T.Q.derive.range := by
      have h1 : (QuotientAddGroup.mk (T.swap.ιKer a) :
          T.swap.Q.derive.ker ⧸ T.swap.Q.norm.range.addSubgroupOf T.swap.Q.derive.ker) = 0 :=
        ha
      rw [tateQuot_mk_eq_zero] at h1
      exact h1
    obtain ⟨b, hb⟩ := ha'
    have hπb : T.π b ∈ T.R.derive.ker := by
      rw [AddMonoidHom.mem_ker, T.derive_π, hb]
      show T.π (T.ι a.1) = 0
      exact T.π_ι a.1
    refine ⟨QuotientAddGroup.mk ⟨T.π b, hπb⟩, ?_⟩
    exact T.connecting_mk_eq_of_rel a.2 ⟨b, rfl, hb.symm⟩

theorem tateCard_mul :
    T.P.tateCard₀ * T.R.tateCard₀ * T.Q.tateCard₁ =
      T.Q.tateCard₀ * T.P.tateCard₁ * T.R.tateCard₁ :=
  card_mul_eq_of_exactCycle
    T.inducedι T.inducedπ T.connecting T.swap.inducedι T.swap.inducedπ T.swap.connecting
    T.exact_at_middle T.exact_at_quot T.exact_at_sub
    T.swap.exact_at_middle T.swap.exact_at_quot T.swap.exact_at_sub

theorem tateCard_mul_of_finite_quot [Finite C] :
    T.P.tateCard₀ * T.Q.tateCard₁ = T.Q.tateCard₀ * T.P.tateCard₁ := by
  have key := T.tateCard_mul
  rw [T.R.tateCard₀_eq_tateCard₁_of_finite] at key
  have hR : T.R.tateCard₁ ≠ 0 := T.R.tateCard₁_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hR) ?_
  calc T.P.tateCard₀ * T.Q.tateCard₁ * T.R.tateCard₁
      = T.P.tateCard₀ * T.R.tateCard₁ * T.Q.tateCard₁ := by ring
    _ = T.Q.tateCard₀ * T.P.tateCard₁ * T.R.tateCard₁ := key

end HerbrandTriple
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple"

section Gates

theorem exactCycle_conclusion_refutable :
    ¬ (Nat.card (ZMod 2) * Nat.card (ZMod 1) * Nat.card (ZMod 1) =
       Nat.card (ZMod 1) * Nat.card (ZMod 1) * Nat.card (ZMod 1)) := by
  simp [Nat.card_eq_fintype_card]

open HerbrandPair in

noncomputable def prodTriple {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    (P : HerbrandPair A) (R : HerbrandPair C) : HerbrandTriple A (A × C) C where
  P := P
  Q := P.prod R
  R := R
  ι := AddMonoidHom.inl A C
  π := AddMonoidHom.snd A C
  ι_injective a b h := by simpa using congrArg Prod.fst h
  π_surjective c := ⟨(0, c), rfl⟩
  exact := by
    ext x
    simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, AddMonoidHom.inl_apply,
      AddMonoidHom.coe_snd, Prod.ext_iff]
    constructor
    · rintro ⟨a, _, hc⟩
      exact hc.symm
    · intro h
      exact ⟨x.1, rfl, h.symm⟩
  derive_ι a := by
    show (P.derive a, R.derive 0) = (P.derive a, 0)
    rw [map_zero]
  norm_ι a := by
    show (P.norm a, R.norm 0) = (P.norm a, 0)
    rw [map_zero]
  derive_π _ := rfl
  norm_π _ := rfl

open HerbrandPair in

theorem tateCard_mul_fires_at_prodTriple {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    (P : HerbrandPair A) (R : HerbrandPair C) :
    (prodTriple P R).P.tateCard₀ * (prodTriple P R).R.tateCard₀ *
        (prodTriple P R).Q.tateCard₁ =
      (prodTriple P R).Q.tateCard₀ * (prodTriple P R).P.tateCard₁ *
        (prodTriple P R).R.tateCard₁ :=
  (prodTriple P R).tateCard_mul

open HerbrandPair in

theorem tateCard_mul_prodTriple_disjoint_route {A C : Type*} [AddCommGroup A]
    [AddCommGroup C] (P : HerbrandPair A) (R : HerbrandPair C) :
    (prodTriple P R).P.tateCard₀ * (prodTriple P R).R.tateCard₀ *
        (prodTriple P R).Q.tateCard₁ =
      (prodTriple P R).Q.tateCard₀ * (prodTriple P R).P.tateCard₁ *
        (prodTriple P R).R.tateCard₁ := by
  show P.tateCard₀ * R.tateCard₀ * (P.prod R).tateCard₁ =
    (P.prod R).tateCard₀ * P.tateCard₁ * R.tateCard₁
  rw [tateCard₀_prod, tateCard₁_prod]
  ring

end Gates
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple"

end Fold_HerbrandQuotientMultiplicative
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple"

section Fold_LocalUnitsCohomology

open Finset

namespace M4aLocalCFT
namespace LocalUnitsCohomology

noncomputable def intCyclicPair (n : ℕ) : HerbrandPair ℤ :=
  HerbrandPair.ofAddAut (1 : AddAut ℤ) n (one_pow n)

@[scoped simp] theorem intCyclicPair_derive_apply (n : ℕ) (a : ℤ) :
    (intCyclicPair n).derive a = 0 := by
  show (HerbrandPair.ofAddAut (1 : AddAut ℤ) n (one_pow n)).derive a = 0
  rw [HerbrandPair.ofAddAut_derive_apply]
  simp

theorem intCyclicPair_norm_apply (n : ℕ) (a : ℤ) :
    (intCyclicPair n).norm a = (n : ℤ) * a := by
  show (HerbrandPair.ofAddAut (1 : AddAut ℤ) n (one_pow n)).norm a = (n : ℤ) * a
  rw [HerbrandPair.ofAddAut_norm_apply]
  simp [Finset.sum_const, Finset.card_range]

theorem tateCard₁_intCyclicPair {n : ℕ} (hn : n ≠ 0) :
    (intCyclicPair n).tateCard₁ = 1 := by
  rw [HerbrandPair.tateCard₁, Nat.card_eq_one_iff_exists]
  have hker : ∀ x : (intCyclicPair n).norm.ker, x = 0 := by
    rintro ⟨x, hx⟩
    rw [AddMonoidHom.mem_ker, intCyclicPair_norm_apply] at hx
    have hnz : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
    exact Subtype.ext (by
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h hnz
      · exact h)
  exact ⟨QuotientAddGroup.mk 0, fun y =>
    QuotientAddGroup.induction_on y fun x => congrArg QuotientAddGroup.mk (hker x)⟩

private noncomputable def reduceModN (n : ℕ) :
    (intCyclicPair n).derive.ker →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (intCyclicPair n).derive.ker.subtype

private theorem reduceModN_surjective (n : ℕ) : Function.Surjective (reduceModN n) := by
  intro z
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective z
  refine ⟨⟨a, ?_⟩, ha⟩
  rw [AddMonoidHom.mem_ker, intCyclicPair_derive_apply]

private theorem reduceModN_ker (n : ℕ) (_hn : n ≠ 0) :
    (reduceModN n).ker
      = (intCyclicPair n).norm.range.addSubgroupOf (intCyclicPair n).derive.ker := by
  haveI : NeZero n := ⟨_hn⟩
  ext ⟨x, hx⟩
  simp only [AddMonoidHom.mem_ker, reduceModN, AddMonoidHom.coe_comp,
    Function.comp_apply, AddSubgroup.coe_subtype, Int.coe_castAddHom,
    AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [intCyclicPair_norm_apply]; exact ha.symm⟩
  · rintro ⟨a, ha⟩
    rw [intCyclicPair_norm_apply] at ha
    exact ⟨a, ha.symm⟩

theorem tateCard₀_intCyclicPair {n : ℕ} (hn : n ≠ 0) :
    (intCyclicPair n).tateCard₀ = n := by
  rw [HerbrandPair.tateCard₀, ← reduceModN_ker n hn]
  rw [Nat.card_congr
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (reduceModN_surjective n)).toEquiv]
  exact Nat.card_zmod n

theorem tateCard₀_intCyclicPair_two : (intCyclicPair 2).tateCard₀ = 2 :=
  tateCard₀_intCyclicPair (by norm_num)

def IsCohTrivial {A : Type*} [AddCommGroup A] (P : HerbrandPair A) : Prop :=
  P.tateCard₀ = 1 ∧ P.tateCard₁ = 1

theorem IsCohTrivial.tateCard_eq {A : Type*} [AddCommGroup A] {P : HerbrandPair A}
    (h : IsCohTrivial P) : P.tateCard₀ = P.tateCard₁ ∧ P.tateCard₁ ≠ 0 :=
  ⟨h.1.trans h.2.symm, h.2 ▸ one_ne_zero⟩

theorem herbrandTrivial_of_finite {A : Type*} [AddCommGroup A] (P : HerbrandPair A)
    [Finite A] : P.tateCard₀ = P.tateCard₁ ∧ P.tateCard₁ ≠ 0 :=
  ⟨P.tateCard₀_eq_tateCard₁_of_finite, P.tateCard₁_ne_zero_of_finite⟩

open HerbrandTriple in

theorem tateCard₀_eq_mul_of_unit_sub {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (T : HerbrandTriple A B C) {n : ℕ}
    (hR₀ : T.R.tateCard₀ = n) (hR₁ : T.R.tateCard₁ = 1)
    (hP : T.P.tateCard₀ = T.P.tateCard₁) (hPne : T.P.tateCard₁ ≠ 0) :
    T.Q.tateCard₀ = n * T.Q.tateCard₁ := by
  have key := T.tateCard_mul
  rw [hR₀, hR₁, hP, mul_one] at key

  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hPne) ?_
  calc T.P.tateCard₁ * T.Q.tateCard₀ = T.Q.tateCard₀ * T.P.tateCard₁ := by ring
    _ = T.P.tateCard₁ * T.R.tateCard₀ * T.Q.tateCard₁ := by rw [hR₀]; exact key.symm
    _ = T.P.tateCard₁ * (T.R.tateCard₀ * T.Q.tateCard₁) := by ring
    _ = T.P.tateCard₁ * (n * T.Q.tateCard₁) := by rw [hR₀]

open HerbrandTriple in

theorem tateCard₀_eq_mul_of_int_quotient {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (T : HerbrandTriple A B ℤ) {n : ℕ} (hn : n ≠ 0) (hR : T.R = intCyclicPair n)
    (hP : T.P.tateCard₀ = T.P.tateCard₁) (hPne : T.P.tateCard₁ ≠ 0) :
    T.Q.tateCard₀ = n * T.Q.tateCard₁ :=
  tateCard₀_eq_mul_of_unit_sub T (by rw [hR]; exact tateCard₀_intCyclicPair hn)
    (by rw [hR]; exact tateCard₁_intCyclicPair hn) hP hPne

section Gates

open HerbrandPair HerbrandTriple

theorem valuationSequence_fires :
    (prodTriple zmodTwoPair (intCyclicPair 3)).Q.tateCard₀
      = 3 * (prodTriple zmodTwoPair (intCyclicPair 3)).Q.tateCard₁ :=
  tateCard₀_eq_mul_of_unit_sub (prodTriple zmodTwoPair (intCyclicPair 3))
    (tateCard₀_intCyclicPair (by norm_num)) (tateCard₁_intCyclicPair (by norm_num))
    zmodTwoPair.tateCard₀_eq_tateCard₁_of_finite
    zmodTwoPair.tateCard₁_ne_zero_of_finite

theorem valuationSequence_disjoint_route :
    (prodTriple zmodTwoPair (intCyclicPair 3)).Q.tateCard₀
      = 3 * (prodTriple zmodTwoPair (intCyclicPair 3)).Q.tateCard₁ := by
  show (zmodTwoPair.prod (intCyclicPair 3)).tateCard₀
      = 3 * (zmodTwoPair.prod (intCyclicPair 3)).tateCard₁
  rw [HerbrandPair.tateCard₀_prod, HerbrandPair.tateCard₁_prod,
    tateCard₀_intCyclicPair (n := 3) (by norm_num),
    tateCard₁_intCyclicPair (n := 3) (by norm_num),
    zmodTwoPair.tateCard₀_eq_tateCard₁_of_finite]
  ring

theorem valuationSequence_sub_load_bearing :
    (prodTriple (intCyclicPair 2) (intCyclicPair 3)).Q.tateCard₀
      ≠ 3 * (prodTriple (intCyclicPair 2) (intCyclicPair 3)).Q.tateCard₁ := by
  show (HerbrandPair.prod (intCyclicPair 2) (intCyclicPair 3)).tateCard₀
      ≠ 3 * (HerbrandPair.prod (intCyclicPair 2) (intCyclicPair 3)).tateCard₁
  rw [HerbrandPair.tateCard₀_prod, HerbrandPair.tateCard₁_prod,
    tateCard₀_intCyclicPair (n := 2) (by norm_num),
    tateCard₀_intCyclicPair (n := 3) (by norm_num),
    tateCard₁_intCyclicPair (n := 2) (by norm_num),
    tateCard₁_intCyclicPair (n := 3) (by norm_num)]
  decide

theorem tateCard₁_intCyclicPair_zero_ne_one : (intCyclicPair 0).tateCard₁ ≠ 1 := by
  intro h
  rw [HerbrandPair.tateCard₁, Nat.card_eq_one_iff_exists] at h
  obtain ⟨c, hc⟩ := h

  have h0 : (0 : ℤ) ∈ (intCyclicPair 0).norm.ker := zero_mem _
  have h1 : (1 : ℤ) ∈ (intCyclicPair 0).norm.ker := by
    rw [AddMonoidHom.mem_ker, intCyclicPair_norm_apply]; simp
  have heq : (QuotientAddGroup.mk (⟨0, h0⟩ : (intCyclicPair 0).norm.ker) :
      (intCyclicPair 0).norm.ker ⧸ (intCyclicPair 0).derive.range.addSubgroupOf
        (intCyclicPair 0).norm.ker) = QuotientAddGroup.mk ⟨1, h1⟩ :=
    (hc _).trans (hc _).symm
  have hmem := QuotientAddGroup.eq.mp heq
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨a, ha⟩ := hmem
  rw [intCyclicPair_derive_apply] at ha
  have hval : ((-(⟨0, h0⟩ : (intCyclicPair 0).norm.ker) + ⟨1, h1⟩ :
      (intCyclicPair 0).norm.ker) : ℤ) = 1 := by
    simp
  rw [hval] at ha
  omega

end Gates
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple"

#print axioms tateCard₀_intCyclicPair
#print axioms tateCard₁_intCyclicPair
#print axioms tateCard₀_intCyclicPair_two
#print axioms IsCohTrivial.tateCard_eq
#print axioms herbrandTrivial_of_finite
#print axioms tateCard₀_eq_mul_of_unit_sub
#print axioms tateCard₀_eq_mul_of_int_quotient
#print axioms valuationSequence_fires
#print axioms valuationSequence_disjoint_route
#print axioms valuationSequence_sub_load_bearing
#print axioms tateCard₁_intCyclicPair_zero_ne_one

end LocalUnitsCohomology
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology"
end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology"

end Fold_LocalUnitsCohomology
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology"

section Fold_InducedModuleCohTrivial

open Finset

namespace M4aLocalCFT

open HerbrandPair LocalUnitsCohomology

namespace InducedModule

variable (n : ℕ) (M : Type*) [AddCommGroup M]

def shiftAut : AddAut (ZMod n → M) where
  toFun f := fun i => f (i + 1)
  invFun f := fun i => f (i - 1)
  left_inv f := funext fun i => congrArg f (by ring)
  right_inv f := funext fun i => congrArg f (by ring)
  map_add' _ _ := rfl

@[scoped simp] theorem shiftAut_apply (f : ZMod n → M) (i : ZMod n) :
    shiftAut n M f i = f (i + 1) := rfl

private theorem _root_.M4aLocalCFT.InducedModule.cast_succ (m : ℕ) : (((m + 1 : ℕ)) : ZMod n) = ((m : ℕ) : ZMod n) + 1 := by
  rw [Nat.cast_add, Nat.cast_one]

p2m_export "M4aLocalCFT.InducedModule" "cast_succ"
theorem shiftAut_pow_apply (k : ℕ) (f : ZMod n → M) (i : ZMod n) :
    ((shiftAut n M) ^ k) f i = f (i + (k : ZMod n)) := by
  induction k generalizing f with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, AddAut.mul_apply', ih, shiftAut_apply, cast_succ n j, ← add_assoc]

theorem shiftAut_pow_n : (shiftAut n M) ^ n = 1 := by
  refine AddEquiv.ext fun f => funext fun i => ?_
  rw [shiftAut_pow_apply, AddAut.one_apply', ZMod.natCast_self, add_zero]

noncomputable def inducedPair : HerbrandPair (ZMod n → M) :=
  HerbrandPair.ofAddAut (shiftAut n M) n (shiftAut_pow_n n M)

theorem inducedPair_derive_apply (f : ZMod n → M) (i : ZMod n) :
    (inducedPair n M).derive f i = f (i + 1) - f i := by
  show (HerbrandPair.ofAddAut (shiftAut n M) n (shiftAut_pow_n n M)).derive f i = _
  rw [HerbrandPair.ofAddAut_derive_apply]
  rfl

theorem inducedPair_norm_apply (f : ZMod n → M) (i : ZMod n) :
    (inducedPair n M).norm f i = ∑ k ∈ Finset.range n, f (i + (k : ZMod n)) := by
  show (HerbrandPair.ofAddAut (shiftAut n M) n (shiftAut_pow_n n M)).norm f i = _
  rw [HerbrandPair.ofAddAut_norm_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => shiftAut_pow_apply n M k f i

omit [AddCommGroup M] in

private theorem apply_natCast_eq_apply_zero (f : ZMod n → M)
    (hf : ∀ j : ZMod n, f (j + 1) = f j) (m : ℕ) : f ((m : ℕ) : ZMod n) = f 0 := by
  induction m with
  | zero => exact congrArg f Nat.cast_zero
  | succ k ih =>
      rw [cast_succ n k, hf]
      exact ih

variable [NeZero n]

theorem eq_const_of_derive_eq_zero {f : ZMod n → M}
    (hf : (inducedPair n M).derive f = 0) (i : ZMod n) : f i = f 0 := by
  have step : ∀ j : ZMod n, f (j + 1) = f j := by
    intro j
    have h := congrFun hf j
    rw [inducedPair_derive_apply, Pi.zero_apply] at h
    exact eq_of_sub_eq_zero h
  obtain ⟨m, -, rfl⟩ : ∃ m, m < n ∧ ((m : ℕ) : ZMod n) = i :=
    ⟨i.val, ZMod.val_lt i, ZMod.natCast_rightInverse i⟩
  exact apply_natCast_eq_apply_zero n M f step m

private def delta (c : M) : ZMod n → M := fun j => if j = 0 then c else 0

private theorem sum_delta (c : M) :
    ∑ k ∈ Finset.range n, delta n M c ((k : ℕ) : ZMod n) = c := by
  have key : (∑ k ∈ Finset.range n, delta n M c ((k : ℕ) : ZMod n))
      = delta n M c (((0 : ℕ)) : ZMod n) := by
    refine Finset.sum_eq_single 0 (fun k hk hk0 => ?_) (fun h => ?_)
    · refine if_neg fun hcast => hk0 ?_
      have hv := ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
      rw [hcast, ZMod.val_zero] at hv
      exact hv.symm
    · exact absurd (Finset.mem_range.mpr (Nat.pos_of_ne_zero (NeZero.ne n))) h
  rw [key]
  show (if (((0 : ℕ)) : ZMod n) = 0 then c else 0) = c
  rw [if_pos Nat.cast_zero]

private theorem norm_delta (c : M) (i : ZMod n) :
    (inducedPair n M).norm (delta n M c) i = c := by
  have hconst : (inducedPair n M).norm (delta n M c) i
      = (inducedPair n M).norm (delta n M c) 0 :=
    eq_const_of_derive_eq_zero n M ((inducedPair n M).derive_norm (delta n M c)) i
  rw [hconst, inducedPair_norm_apply]
  simp only [zero_add]
  exact sum_delta n M c

theorem tateCard₀_inducedPair : (inducedPair n M).tateCard₀ = 1 := by
  rw [HerbrandPair.tateCard₀, Nat.card_eq_one_iff_exists]
  refine ⟨QuotientAddGroup.mk 0, fun y => QuotientAddGroup.induction_on y fun x => ?_⟩
  refine (QuotientAddGroup.eq.mpr ?_).symm
  rw [AddSubgroup.mem_addSubgroupOf]
  refine ⟨delta n M (x.1 0), ?_⟩
  have hx : ((-(0 : (inducedPair n M).derive.ker) + x :
      (inducedPair n M).derive.ker) : ZMod n → M) = x.1 := by simp
  rw [hx]
  funext i
  rw [norm_delta n M (x.1 0) i]
  exact (eq_const_of_derive_eq_zero n M (AddMonoidHom.mem_ker.mp x.2) i).symm

private theorem derive_partialSum (g : ZMod n → M)
    (hg : ∑ k ∈ Finset.range n, g ((k : ℕ) : ZMod n) = 0) (i : ZMod n) :
    (∑ k ∈ Finset.range ((i + 1).val), g ((k : ℕ) : ZMod n))
      - ∑ k ∈ Finset.range i.val, g ((k : ℕ) : ZMod n) = g i := by
  obtain ⟨m, hm, rfl⟩ : ∃ m, m < n ∧ ((m : ℕ) : ZMod n) = i :=
    ⟨i.val, ZMod.val_lt i, ZMod.natCast_rightInverse i⟩
  rw [ZMod.val_cast_of_lt hm, ← cast_succ n m]
  rcases Nat.lt_or_ge (m + 1) n with hlt | hge
  ·
    rw [ZMod.val_cast_of_lt hlt, Finset.sum_range_succ]
    abel
  ·

    have hmn : m + 1 = n := by omega
    have h1 : (((m + 1 : ℕ)) : ZMod n) = 0 := by rw [hmn, ZMod.natCast_self]
    have hsplit : (∑ k ∈ Finset.range m, g ((k : ℕ) : ZMod n)) + g ((m : ℕ) : ZMod n)
        = ∑ k ∈ Finset.range n, g ((k : ℕ) : ZMod n) := by
      rw [← Finset.sum_range_succ (fun k => g ((k : ℕ) : ZMod n)) m, hmn]
    rw [h1, ZMod.val_zero, Finset.sum_range_zero]
    rw [← hsplit] at hg
    rw [← hg]
    abel

theorem tateCard₁_inducedPair : (inducedPair n M).tateCard₁ = 1 := by
  rw [HerbrandPair.tateCard₁, Nat.card_eq_one_iff_exists]
  refine ⟨QuotientAddGroup.mk 0, fun y => QuotientAddGroup.induction_on y fun x => ?_⟩
  refine (QuotientAddGroup.eq.mpr ?_).symm
  rw [AddSubgroup.mem_addSubgroupOf]
  have hker : ∑ k ∈ Finset.range n, x.1 ((k : ℕ) : ZMod n) = 0 := by
    have h := congrFun (AddMonoidHom.mem_ker.mp x.2) 0
    rw [inducedPair_norm_apply, Pi.zero_apply] at h
    simpa using h
  refine ⟨fun j => ∑ k ∈ Finset.range j.val, x.1 ((k : ℕ) : ZMod n), ?_⟩
  have hx : ((-(0 : (inducedPair n M).norm.ker) + x :
      (inducedPair n M).norm.ker) : ZMod n → M) = x.1 := by simp
  rw [hx]
  funext i
  rw [inducedPair_derive_apply]
  exact derive_partialSum n M x.1 hker i

theorem isCohTrivial_inducedPair : IsCohTrivial (inducedPair n M) :=
  ⟨tateCard₀_inducedPair n M, tateCard₁_inducedPair n M⟩

theorem isCohTrivial_zmodPower (r : ℕ) : IsCohTrivial (inducedPair n (Fin r → ℤ)) :=
  isCohTrivial_inducedPair n (Fin r → ℤ)

theorem inducedPair_carrier_infinite : Infinite (ZMod 3 → ℤ) :=
  Infinite.of_injective (fun (k : ℤ) (_ : ZMod 3) => k) fun _ _ h => congrFun h 0

theorem shiftAut_ne_one : shiftAut 2 ℤ ≠ 1 := by
  intro h
  have h0 : (fun (j : ZMod 2) => if j = 0 then (1 : ℤ) else 0) ((0 : ZMod 2) + 1)
      = (fun (j : ZMod 2) => if j = 0 then (1 : ℤ) else 0) (0 : ZMod 2) :=
    congrFun (congrArg (fun σ : AddAut (ZMod 2 → ℤ) =>
      σ (fun j => if j = 0 then (1 : ℤ) else 0)) h) (0 : ZMod 2)
  exact absurd h0 (by decide)

theorem isCohTrivial_inducedPair_two : IsCohTrivial (inducedPair 2 ℤ) :=
  isCohTrivial_inducedPair 2 ℤ

theorem isCohTrivial_inducedPair_three : IsCohTrivial (inducedPair 3 ℤ) :=
  isCohTrivial_inducedPair 3 ℤ

theorem isCohTrivial_zmodPower_two_three : IsCohTrivial (inducedPair 2 (Fin 3 → ℤ)) :=
  isCohTrivial_zmodPower 2 3

end InducedModule
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

end Fold_InducedModuleCohTrivial
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

section Fold_HerbrandLatticeComparison

namespace M4aLocalCFT

universe u

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

namespace HerbrandPair

noncomputable def descendToQuotient (Q : HerbrandPair B) (S : AddSubgroup B)
    (hd : ∀ b ∈ S, Q.derive b ∈ S) (hn : ∀ b ∈ S, Q.norm b ∈ S) :
    HerbrandPair (B ⧸ S) where
  derive := QuotientAddGroup.map S S Q.derive hd
  norm := QuotientAddGroup.map S S Q.norm hn
  derive_norm := by
    intro x
    refine QuotientAddGroup.induction_on x fun b => ?_
    show QuotientAddGroup.map S S Q.derive hd
        (QuotientAddGroup.map S S Q.norm hn (QuotientAddGroup.mk b)) = 0
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, Q.derive_norm,
      QuotientAddGroup.mk_zero]
  norm_derive := by
    intro x
    refine QuotientAddGroup.induction_on x fun b => ?_
    show QuotientAddGroup.map S S Q.norm hn
        (QuotientAddGroup.map S S Q.derive hd (QuotientAddGroup.mk b)) = 0
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, Q.norm_derive,
      QuotientAddGroup.mk_zero]

@[scoped simp] theorem descendToQuotient_derive_mk (Q : HerbrandPair B) (S : AddSubgroup B)
    (hd : ∀ b ∈ S, Q.derive b ∈ S) (hn : ∀ b ∈ S, Q.norm b ∈ S) (b : B) :
    (Q.descendToQuotient S hd hn).derive (QuotientAddGroup.mk b)
      = QuotientAddGroup.mk (Q.derive b) :=
  rfl

@[scoped simp] theorem descendToQuotient_norm_mk (Q : HerbrandPair B) (S : AddSubgroup B)
    (hd : ∀ b ∈ S, Q.derive b ∈ S) (hn : ∀ b ∈ S, Q.norm b ∈ S) (b : B) :
    (Q.descendToQuotient S hd hn).norm (QuotientAddGroup.mk b)
      = QuotientAddGroup.mk (Q.norm b) :=
  rfl

end HerbrandPair
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

section Stability

variable (P : HerbrandPair A) (Q : HerbrandPair B) (f : A →+ B)

theorem rangeStable_derive (hd : ∀ a, Q.derive (f a) = f (P.derive a)) :
    ∀ b ∈ f.range, Q.derive b ∈ f.range := by
  rintro b ⟨a, rfl⟩
  exact ⟨P.derive a, (hd a).symm⟩

theorem rangeStable_norm (hn : ∀ a, Q.norm (f a) = f (P.norm a)) :
    ∀ b ∈ f.range, Q.norm b ∈ f.range := by
  rintro b ⟨a, rfl⟩
  exact ⟨P.norm a, (hn a).symm⟩

end Stability
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

namespace HerbrandTriple

noncomputable def ofInjectiveIntertwining (P : HerbrandPair A) (Q : HerbrandPair B)
    (f : A →+ B) (hf : Function.Injective f)
    (hd : ∀ a, Q.derive (f a) = f (P.derive a))
    (hn : ∀ a, Q.norm (f a) = f (P.norm a)) :
    HerbrandTriple A B (B ⧸ f.range) where
  P := P
  Q := Q
  R := Q.descendToQuotient f.range (rangeStable_derive P Q f hd) (rangeStable_norm P Q f hn)
  ι := f
  π := QuotientAddGroup.mk' f.range
  ι_injective := hf
  π_surjective := QuotientAddGroup.mk'_surjective f.range
  exact := (QuotientAddGroup.ker_mk' f.range).symm
  derive_ι := hd
  norm_ι := hn
  derive_π := fun b => (HerbrandPair.descendToQuotient_derive_mk Q f.range
    (rangeStable_derive P Q f hd) (rangeStable_norm P Q f hn) b).symm
  norm_π := fun b => (HerbrandPair.descendToQuotient_norm_mk Q f.range
    (rangeStable_derive P Q f hd) (rangeStable_norm P Q f hn) b).symm

end HerbrandTriple
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

theorem tateCard_cross_eq_of_injective (P : HerbrandPair A) (Q : HerbrandPair B)
    (f : A →+ B) (hf : Function.Injective f)
    (hd : ∀ a, Q.derive (f a) = f (P.derive a))
    (hn : ∀ a, Q.norm (f a) = f (P.norm a)) [Finite (B ⧸ f.range)] :
    P.tateCard₀ * Q.tateCard₁ = Q.tateCard₀ * P.tateCard₁ :=
  (HerbrandTriple.ofInjectiveIntertwining P Q f hf hd hn).tateCard_mul_of_finite_quot

theorem tateCard_cross_eq_of_addEquiv (P : HerbrandPair A) (Q : HerbrandPair B)
    (e : A ≃+ B)
    (hd : ∀ a, Q.derive (e a) = e (P.derive a))
    (hn : ∀ a, Q.norm (e a) = e (P.norm a)) :
    P.tateCard₀ * Q.tateCard₁ = Q.tateCard₀ * P.tateCard₁ := by
  haveI : Subsingleton (B ⧸ (e : A →+ B).range) := by
    refine ⟨fun x y => ?_⟩
    refine QuotientAddGroup.induction_on x fun b => QuotientAddGroup.induction_on y
      fun c => ?_
    rw [QuotientAddGroup.eq]
    exact ⟨e.symm (-b + c), by simp⟩
  haveI : Finite (B ⧸ (e : A →+ B).range) := Finite.of_subsingleton
  exact tateCard_cross_eq_of_injective P Q (e : A →+ B) e.injective hd hn

section Gates

open LocalUnitsCohomology

theorem inl_intertwines {C : Type u} [AddCommGroup C] (P : HerbrandPair A)
    (R : HerbrandPair C) :
    (∀ a, (P.prod R).derive (AddMonoidHom.inl A C a) = AddMonoidHom.inl A C (P.derive a))
      ∧ ∀ a, (P.prod R).norm (AddMonoidHom.inl A C a) = AddMonoidHom.inl A C (P.norm a) :=
  ⟨fun a => by show (P.derive a, R.derive 0) = (P.derive a, 0); rw [map_zero],
   fun a => by show (P.norm a, R.norm 0) = (P.norm a, 0); rw [map_zero]⟩

theorem finite_quotient_range_inl {C : Type u} [AddCommGroup C] [Finite C] :
    Finite ((A × C) ⧸ (AddMonoidHom.inl A C).range) := by
  have hrk : (AddMonoidHom.inl A C).range = (AddMonoidHom.snd A C).ker := by
    ext x
    simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, AddMonoidHom.inl_apply,
      AddMonoidHom.coe_snd, Prod.ext_iff]
    constructor
    · rintro ⟨a, _, hc⟩
      exact hc.symm
    · intro h
      exact ⟨x.1, rfl, h.symm⟩
  rw [hrk]
  exact Finite.of_equiv C
    (QuotientAddGroup.quotientKerEquivOfSurjective (AddMonoidHom.snd A C)
      (fun c => ⟨(0, c), rfl⟩)).symm.toEquiv

theorem gate_lattice_cross_fires_at_inl :
    (intCyclicPair 2).tateCard₀ * ((intCyclicPair 2).prod zmodTwoPair).tateCard₁
      = ((intCyclicPair 2).prod zmodTwoPair).tateCard₀ * (intCyclicPair 2).tateCard₁ := by
  haveI := finite_quotient_range_inl (A := ℤ) (C := ZMod 2)
  exact tateCard_cross_eq_of_injective (intCyclicPair 2)
    ((intCyclicPair 2).prod zmodTwoPair) (AddMonoidHom.inl ℤ (ZMod 2))
    (fun a b h => by simpa using congrArg Prod.fst h)
    (inl_intertwines (intCyclicPair 2) zmodTwoPair).1
    (inl_intertwines (intCyclicPair 2) zmodTwoPair).2

theorem gate_lattice_cross_inl_disjoint_route :
    (intCyclicPair 2).tateCard₀ * ((intCyclicPair 2).prod zmodTwoPair).tateCard₁
      = ((intCyclicPair 2).prod zmodTwoPair).tateCard₀ * (intCyclicPair 2).tateCard₁ := by
  rw [HerbrandPair.tateCard₀_prod, HerbrandPair.tateCard₁_prod,
    zmodTwoPair.tateCard₀_eq_tateCard₁_of_finite]
  ring

theorem gate_lattice_finite_cokernel_load_bearing :
    Function.Injective (AddMonoidHom.inl ℤ ℤ)
      ∧ (∀ a, ((intCyclicPair 2).prod (intCyclicPair 2)).derive (AddMonoidHom.inl ℤ ℤ a)
          = AddMonoidHom.inl ℤ ℤ ((intCyclicPair 2).derive a))
      ∧ ¬ ((intCyclicPair 2).tateCard₀
            * ((intCyclicPair 2).prod (intCyclicPair 2)).tateCard₁
          = ((intCyclicPair 2).prod (intCyclicPair 2)).tateCard₀
            * (intCyclicPair 2).tateCard₁) := by
  refine ⟨fun a b h => by simpa using congrArg Prod.fst h,
    (inl_intertwines (intCyclicPair 2) (intCyclicPair 2)).1, ?_⟩
  rw [HerbrandPair.tateCard₀_prod, HerbrandPair.tateCard₁_prod,
    tateCard₀_intCyclicPair (by norm_num), tateCard₁_intCyclicPair (by norm_num)]
  omega

theorem gate_lattice_norm_intertwining_load_bearing :
    Function.Injective (AddMonoidHom.id ℤ)
      ∧ (∀ a, (intCyclicPair 3).derive (AddMonoidHom.id ℤ a)
          = AddMonoidHom.id ℤ ((intCyclicPair 2).derive a))
      ∧ Finite (ℤ ⧸ (AddMonoidHom.id ℤ).range)
      ∧ ¬ ((intCyclicPair 2).tateCard₀ * (intCyclicPair 3).tateCard₁
          = (intCyclicPair 3).tateCard₀ * (intCyclicPair 2).tateCard₁) := by
  refine ⟨fun a b h => h, ?_, ?_, ?_⟩
  · intro a
    rw [intCyclicPair_derive_apply, intCyclicPair_derive_apply, map_zero]
  · haveI : Subsingleton (ℤ ⧸ (AddMonoidHom.id ℤ).range) := by
      refine ⟨fun x y => ?_⟩
      refine QuotientAddGroup.induction_on x fun b => QuotientAddGroup.induction_on y
        fun c => ?_
      rw [QuotientAddGroup.eq]
      exact ⟨-b + c, rfl⟩
    exact Finite.of_subsingleton
  · rw [tateCard₀_intCyclicPair (by norm_num), tateCard₁_intCyclicPair (by norm_num),
      tateCard₀_intCyclicPair (by norm_num), tateCard₁_intCyclicPair (by norm_num)]
    omega

theorem gate_same_rank_insufficient :
    ¬ ((InducedModule.inducedPair 2 ℤ).tateCard₀
          * ((intCyclicPair 2).prod (intCyclicPair 2)).tateCard₁
        = ((intCyclicPair 2).prod (intCyclicPair 2)).tateCard₀
          * (InducedModule.inducedPair 2 ℤ).tateCard₁) := by
  rw [(InducedModule.isCohTrivial_inducedPair 2 ℤ).1,
    (InducedModule.isCohTrivial_inducedPair 2 ℤ).2,
    HerbrandPair.tateCard₀_prod, HerbrandPair.tateCard₁_prod,
    tateCard₀_intCyclicPair (by norm_num), tateCard₁_intCyclicPair (by norm_num)]
  norm_num

theorem gate_lattice_cross_refl (P : HerbrandPair A) :
    P.tateCard₀ * P.tateCard₁ = P.tateCard₀ * P.tateCard₁ :=
  tateCard_cross_eq_of_addEquiv P P (AddEquiv.refl A) (fun _ => rfl) (fun _ => rfl)

end Gates
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

end Fold_HerbrandLatticeComparison
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

section Fold_DenominatorClearing

namespace M4aLocalCFT

universe u

open AddSubgroup

variable {A B V : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]

def nsmulHom (n : ℕ) : B →+ B where
  toFun b := n • b
  map_zero' := nsmul_zero n
  map_add' x y := nsmul_add x y n

@[scoped simp] theorem nsmulHom_apply (n : ℕ) (b : B) : nsmulHom n b = n • b := rfl

theorem forall_map_mem_of_closure_eq_top {W : Type u} [AddCommGroup W]
    (φ : B →+ W) (S : AddSubgroup W) (s : Set B)
    (hs : AddSubgroup.closure s = ⊤) (h : ∀ b ∈ s, φ b ∈ S) (b : B) : φ b ∈ S := by
  have hle : (⊤ : AddSubgroup B) ≤ S.comap φ := by
    rw [← hs]
    exact (AddSubgroup.closure_le _).mpr h
  exact hle (AddSubgroup.mem_top b)

theorem exists_uniform_denominator (ιA : A →+ V) (ιB : B →+ V)
    (s : Finset A) (hs : AddSubgroup.closure (s : Set A) = ⊤)
    (h : ∀ a ∈ s, ∃ n : ℕ, n ≠ 0 ∧ n • ιA a ∈ ιB.range) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ a : A, d • ιA a ∈ ιB.range := by
  classical

  have key : ∀ t : Finset A, (∀ a ∈ t, ∃ n : ℕ, n ≠ 0 ∧ n • ιA a ∈ ιB.range) →
      ∃ d : ℕ, d ≠ 0 ∧ ∀ a ∈ t, d • ιA a ∈ ιB.range := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact fun _ => ⟨1, one_ne_zero, fun a ha => absurd ha (Finset.notMem_empty a)⟩
    | @insert a t _ ih =>
      intro ht
      obtain ⟨d, hd, hdmem⟩ := ih fun x hx => ht x (Finset.mem_insert_of_mem hx)
      obtain ⟨m, hm, hmmem⟩ := ht a (Finset.mem_insert_self a t)
      refine ⟨m * d, Nat.mul_ne_zero hm hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm, mul_smul]
        exact nsmul_mem hmmem d
      · rw [mul_smul]
        exact nsmul_mem (hdmem x hx) m
  obtain ⟨d, hd, hdmem⟩ := key s h
  refine ⟨d, hd, ?_⟩
  intro a
  exact forall_map_mem_of_closure_eq_top ((nsmulHom d).comp ιA) ιB.range (s : Set A) hs
    (fun x hx => hdmem x hx) a

section ClearDenominator

variable (ιA : A →+ V) (ιB : B →+ V) (hιB : Function.Injective ιB)
  (d : ℕ) (hmem : ∀ a : A, d • ιA a ∈ ιB.range)

noncomputable def clearDenominator : A →+ B where
  toFun a := (AddMonoidHom.mem_range.mp (hmem a)).choose
  map_zero' := hιB <| by
    rw [(AddMonoidHom.mem_range.mp (hmem 0)).choose_spec, map_zero, smul_zero, map_zero]
  map_add' x y := hιB <| by
    rw [map_add ιB ((AddMonoidHom.mem_range.mp (hmem x)).choose),
      (AddMonoidHom.mem_range.mp (hmem (x + y))).choose_spec,
      (AddMonoidHom.mem_range.mp (hmem x)).choose_spec,
      (AddMonoidHom.mem_range.mp (hmem y)).choose_spec, map_add, smul_add]

theorem ιB_clearDenominator (a : A) :
    ιB (clearDenominator ιA ιB hιB d hmem a) = d • ιA a :=
  (AddMonoidHom.mem_range.mp (hmem a)).choose_spec

theorem clearDenominator_eq_of_ιB_eq {a : A} {b : B} (hb : ιB b = d • ιA a) :
    clearDenominator ιA ιB hιB d hmem a = b :=
  hιB (by rw [ιB_clearDenominator, hb])

theorem clearDenominator_injective [Module ℚ V] (hιA : Function.Injective ιA)
    (hd : d ≠ 0) : Function.Injective (clearDenominator ιA ιB hιB d hmem) := by
  intro x y hxy
  apply hιA
  have h1 : d • ιA x = d • ιA y := by
    rw [← ιB_clearDenominator ιA ιB hιB d hmem x, ← ιB_clearDenominator ιA ιB hιB d hmem y,
      hxy]
  have h2 : ((d : ℚ)) • ιA x = ((d : ℚ)) • ιA y := by
    rw [Nat.cast_smul_eq_nsmul ℚ d (ιA x), Nat.cast_smul_eq_nsmul ℚ d (ιA y)]
    exact h1
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  calc ιA x = (d : ℚ)⁻¹ • ((d : ℚ) • ιA x) := (inv_smul_smul₀ hd' (ιA x)).symm
    _ = (d : ℚ)⁻¹ • ((d : ℚ) • ιA y) := by rw [h2]
    _ = ιA y := inv_smul_smul₀ hd' (ιA y)

theorem clearDenominator_comm (TA : A →+ A) (TB : B →+ B) (TV : V →+ V)
    (hA : ∀ a, TV (ιA a) = ιA (TA a)) (hB : ∀ b, TV (ιB b) = ιB (TB b)) (a : A) :
    TB (clearDenominator ιA ιB hιB d hmem a)
      = clearDenominator ιA ιB hιB d hmem (TA a) := by
  apply hιB
  rw [← hB, ιB_clearDenominator ιA ιB hιB d hmem a,
    ιB_clearDenominator ιA ιB hιB d hmem (TA a), map_nsmul, hA]

theorem exists_uniform_nsmul_mem_range_clearDenominator (hd : d ≠ 0)
    (t : Finset B) (ht : AddSubgroup.closure (t : Set B) = ⊤)
    (h : ∀ b ∈ t, ∃ n : ℕ, n ≠ 0 ∧ n • ιB b ∈ ιA.range) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ b : B, N • b ∈ (clearDenominator ιA ιB hιB d hmem).range := by
  obtain ⟨m, hm, hmmem⟩ := exists_uniform_denominator ιB ιA t ht h
  refine ⟨d * m, Nat.mul_ne_zero hd hm, ?_⟩
  intro b
  obtain ⟨a₀, ha₀⟩ := AddMonoidHom.mem_range.mp (hmmem b)
  refine AddMonoidHom.mem_range.mpr ⟨a₀, ?_⟩
  apply hιB
  rw [ιB_clearDenominator ιA ιB hιB d hmem a₀, ha₀, ← mul_smul, ← map_nsmul]

theorem finite_quotient_range_clearDenominator (hd : d ≠ 0)
    (t : Finset B) (ht : AddSubgroup.closure (t : Set B) = ⊤)
    (h : ∀ b ∈ t, ∃ n : ℕ, n ≠ 0 ∧ n • ιB b ∈ ιA.range) :
    Finite (B ⧸ (clearDenominator ιA ιB hιB d hmem).range) := by
  obtain ⟨N, hN, hNmem⟩ :=
    exists_uniform_nsmul_mem_range_clearDenominator ιA ιB hιB d hmem hd t ht h
  haveI : AddGroup.FG B := AddGroup.fg_iff.mpr ⟨(t : Set B), ht, t.finite_toSet⟩
  haveI : AddGroup.FG (B ⧸ (clearDenominator ιA ιB hιB d hmem).range) :=
    AddGroup.fg_of_surjective
      (f := QuotientAddGroup.mk' (clearDenominator ιA ιB hιB d hmem).range)
      (QuotientAddGroup.mk'_surjective _)
  refine AddCommGroup.finite_of_fg_torsion _ ?_
  intro x
  refine QuotientAddGroup.induction_on x fun b => ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, Nat.pos_of_ne_zero hN, ?_⟩
  show N • (QuotientAddGroup.mk' (clearDenominator ιA ιB hιB d hmem).range) b = 0
  rw [← map_nsmul]
  exact (QuotientAddGroup.eq_zero_iff _).mpr (hNmem b)

end ClearDenominator
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

theorem exists_intertwining_injective_of_rational_equiv [Module ℚ V]
    (P : HerbrandPair A) (Q : HerbrandPair B) (R : HerbrandPair V)
    (ιA : A →+ V) (ιB : B →+ V)
    (hιA : Function.Injective ιA) (hιB : Function.Injective ιB)
    (hdA : ∀ a, R.derive (ιA a) = ιA (P.derive a))
    (hnA : ∀ a, R.norm (ιA a) = ιA (P.norm a))
    (hdB : ∀ b, R.derive (ιB b) = ιB (Q.derive b))
    (hnB : ∀ b, R.norm (ιB b) = ιB (Q.norm b))
    (s : Finset A) (hs : AddSubgroup.closure (s : Set A) = ⊤)
    (hden : ∀ a ∈ s, ∃ n : ℕ, n ≠ 0 ∧ n • ιA a ∈ ιB.range)
    (t : Finset B) (ht : AddSubgroup.closure (t : Set B) = ⊤)
    (hden' : ∀ b ∈ t, ∃ n : ℕ, n ≠ 0 ∧ n • ιB b ∈ ιA.range) :
    ∃ f : A →+ B, Function.Injective f
      ∧ (∀ a, Q.derive (f a) = f (P.derive a))
      ∧ (∀ a, Q.norm (f a) = f (P.norm a))
      ∧ Finite (B ⧸ f.range) := by
  obtain ⟨d, hd, hmem⟩ := exists_uniform_denominator ιA ιB s hs hden
  exact ⟨clearDenominator ιA ιB hιB d hmem,
    clearDenominator_injective ιA ιB hιB d hmem hιA hd,
    clearDenominator_comm ιA ιB hιB d hmem P.derive Q.derive R.derive hdA hdB,
    clearDenominator_comm ιA ιB hιB d hmem P.norm Q.norm R.norm hnA hnB,
    finite_quotient_range_clearDenominator ιA ιB hιB d hmem hd t ht hden'⟩

theorem tateCard_cross_eq_of_rational_equiv [Module ℚ V]
    (P : HerbrandPair A) (Q : HerbrandPair B) (R : HerbrandPair V)
    (ιA : A →+ V) (ιB : B →+ V)
    (hιA : Function.Injective ιA) (hιB : Function.Injective ιB)
    (hdA : ∀ a, R.derive (ιA a) = ιA (P.derive a))
    (hnA : ∀ a, R.norm (ιA a) = ιA (P.norm a))
    (hdB : ∀ b, R.derive (ιB b) = ιB (Q.derive b))
    (hnB : ∀ b, R.norm (ιB b) = ιB (Q.norm b))
    (s : Finset A) (hs : AddSubgroup.closure (s : Set A) = ⊤)
    (hden : ∀ a ∈ s, ∃ n : ℕ, n ≠ 0 ∧ n • ιA a ∈ ιB.range)
    (t : Finset B) (ht : AddSubgroup.closure (t : Set B) = ⊤)
    (hden' : ∀ b ∈ t, ∃ n : ℕ, n ≠ 0 ∧ n • ιB b ∈ ιA.range) :
    P.tateCard₀ * Q.tateCard₁ = Q.tateCard₀ * P.tateCard₁ := by
  obtain ⟨f, hf, hfd, hfn, hfin⟩ := exists_intertwining_injective_of_rational_equiv
    P Q R ιA ιB hιA hιB hdA hnA hdB hnB s hs hden t ht hden'
  haveI := hfin
  exact tateCard_cross_eq_of_injective P Q f hf hfd hfn

section Gates

noncomputable def intSwapPair : HerbrandPair (ℤ × ℤ) where
  derive :=
    { toFun := fun p => (p.2 - p.1, p.1 - p.2)
      map_zero' := by
        show ((0 : ℤ) - 0, (0 : ℤ) - 0) = (0, 0)
        simp
      map_add' := fun p q => by
        show (p.2 + q.2 - (p.1 + q.1), p.1 + q.1 - (p.2 + q.2))
          = (p.2 - p.1 + (q.2 - q.1), p.1 - p.2 + (q.1 - q.2))
        rw [Prod.mk.injEq]
        exact ⟨by ring, by ring⟩ }
  norm :=
    { toFun := fun p => (p.1 + p.2, p.1 + p.2)
      map_zero' := by
        show ((0 : ℤ) + 0, (0 : ℤ) + 0) = (0, 0)
        simp
      map_add' := fun p q => by
        show (p.1 + q.1 + (p.2 + q.2), p.1 + q.1 + (p.2 + q.2))
          = (p.1 + p.2 + (q.1 + q.2), p.1 + p.2 + (q.1 + q.2))
        rw [Prod.mk.injEq]
        exact ⟨by ring, by ring⟩ }
  derive_norm := fun p => by
    show ((p.1 + p.2) - (p.1 + p.2), (p.1 + p.2) - (p.1 + p.2)) = (0, 0)
    simp
  norm_derive := fun p => by
    show ((p.2 - p.1) + (p.1 - p.2), (p.2 - p.1) + (p.1 - p.2)) = (0, 0)
    rw [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

noncomputable def intDiagPair : HerbrandPair (ℤ × ℤ) where
  derive :=
    { toFun := fun p => (0, -(2 * p.2))
      map_zero' := by
        show ((0 : ℤ), -(2 * (0 : ℤ))) = (0, 0)
        simp
      map_add' := fun p q => by
        show ((0 : ℤ), -(2 * (p.2 + q.2))) = ((0 : ℤ) + 0, -(2 * p.2) + -(2 * q.2))
        rw [Prod.mk.injEq]
        exact ⟨by ring, by ring⟩ }
  norm :=
    { toFun := fun p => (2 * p.1, 0)
      map_zero' := by
        show (2 * (0 : ℤ), (0 : ℤ)) = (0, 0)
        simp
      map_add' := fun p q => by
        show (2 * (p.1 + q.1), (0 : ℤ)) = (2 * p.1 + 2 * q.1, (0 : ℤ) + 0)
        rw [Prod.mk.injEq]
        exact ⟨by ring, by ring⟩ }
  derive_norm := fun p => by
    show ((0 : ℤ), -(2 * (0 : ℤ))) = (0, 0)
    simp
  norm_derive := fun p => by
    show (2 * (0 : ℤ), (0 : ℤ)) = (0, 0)
    simp

noncomputable def ratDiagPair : HerbrandPair (ℚ × ℚ) where
  derive :=
    { toFun := fun p => (0, -(2 * p.2))
      map_zero' := by
        show ((0 : ℚ), -(2 * (0 : ℚ))) = (0, 0)
        simp
      map_add' := fun p q => by
        show ((0 : ℚ), -(2 * (p.2 + q.2))) = ((0 : ℚ) + 0, -(2 * p.2) + -(2 * q.2))
        rw [Prod.mk.injEq]
        exact ⟨by ring, by ring⟩ }
  norm :=
    { toFun := fun p => (2 * p.1, 0)
      map_zero' := by
        show (2 * (0 : ℚ), (0 : ℚ)) = (0, 0)
        simp
      map_add' := fun p q => by
        show (2 * (p.1 + q.1), (0 : ℚ)) = (2 * p.1 + 2 * q.1, (0 : ℚ) + 0)
        rw [Prod.mk.injEq]
        exact ⟨by ring, by ring⟩ }
  derive_norm := fun p => by
    show ((0 : ℚ), -(2 * (0 : ℚ))) = (0, 0)
    simp
  norm_derive := fun p => by
    show (2 * (0 : ℚ), (0 : ℚ)) = (0, 0)
    simp

noncomputable def eigenbasisHom : ℤ × ℤ →+ ℚ × ℚ where
  toFun p := (((p.1 : ℚ) + (p.2 : ℚ)) / 2, ((p.1 : ℚ) - (p.2 : ℚ)) / 2)
  map_zero' := by
    show ((((0 : ℤ) : ℚ) + ((0 : ℤ) : ℚ)) / 2, (((0 : ℤ) : ℚ) - ((0 : ℤ) : ℚ)) / 2) = (0, 0)
    norm_num
  map_add' p q := by
    show ((((p.1 + q.1 : ℤ) : ℚ) + ((p.2 + q.2 : ℤ) : ℚ)) / 2,
          (((p.1 + q.1 : ℤ) : ℚ) - ((p.2 + q.2 : ℤ) : ℚ)) / 2)
      = (((p.1 : ℚ) + (p.2 : ℚ)) / 2 + ((q.1 : ℚ) + (q.2 : ℚ)) / 2,
         ((p.1 : ℚ) - (p.2 : ℚ)) / 2 + ((q.1 : ℚ) - (q.2 : ℚ)) / 2)
    rw [Prod.mk.injEq]
    push_cast
    exact ⟨by ring, by ring⟩

noncomputable def intCastHom₂ : ℤ × ℤ →+ ℚ × ℚ where
  toFun p := ((p.1 : ℚ), (p.2 : ℚ))
  map_zero' := by
    show ((((0 : ℤ)) : ℚ), (((0 : ℤ)) : ℚ)) = (0, 0)
    norm_num
  map_add' p q := by
    show (((p.1 + q.1 : ℤ) : ℚ), ((p.2 + q.2 : ℤ) : ℚ)) = ((p.1 : ℚ) + (q.1 : ℚ), (p.2 : ℚ) + (q.2 : ℚ))
    rw [Prod.mk.injEq]
    push_cast
    exact ⟨rfl, rfl⟩

@[scoped simp] theorem eigenbasisHom_apply (p : ℤ × ℤ) :
    eigenbasisHom p = (((p.1 : ℚ) + (p.2 : ℚ)) / 2, ((p.1 : ℚ) - (p.2 : ℚ)) / 2) := rfl

@[scoped simp] theorem intCastHom₂_apply (p : ℤ × ℤ) :
    intCastHom₂ p = ((p.1 : ℚ), (p.2 : ℚ)) := rfl

theorem intCastHom₂_injective : Function.Injective intCastHom₂ := by
  intro p q h
  have h1 : ((p.1 : ℚ), (p.2 : ℚ)) = ((q.1 : ℚ), (q.2 : ℚ)) := h
  rw [Prod.mk.injEq] at h1
  rw [Prod.ext_iff]
  exact ⟨Int.cast_injective h1.1, Int.cast_injective h1.2⟩

theorem eigenbasisHom_injective : Function.Injective eigenbasisHom := by
  intro p q h
  have h1 : (((p.1 : ℚ) + (p.2 : ℚ)) / 2, ((p.1 : ℚ) - (p.2 : ℚ)) / 2)
      = (((q.1 : ℚ) + (q.2 : ℚ)) / 2, ((q.1 : ℚ) - (q.2 : ℚ)) / 2) := h
  rw [Prod.mk.injEq] at h1
  obtain ⟨ha, hb⟩ := h1
  have hsum : (p.1 : ℚ) + (p.2 : ℚ) = (q.1 : ℚ) + (q.2 : ℚ) := by
    have := congrArg (fun z => z * 2) ha
    simpa [div_mul_cancel₀] using this
  have hdiff : (p.1 : ℚ) - (p.2 : ℚ) = (q.1 : ℚ) - (q.2 : ℚ) := by
    have := congrArg (fun z => z * 2) hb
    simpa [div_mul_cancel₀] using this
  have hp1 : (p.1 : ℚ) = (q.1 : ℚ) := by linarith
  have hp2 : (p.2 : ℚ) = (q.2 : ℚ) := by linarith
  rw [Prod.ext_iff]
  exact ⟨Int.cast_injective hp1, Int.cast_injective hp2⟩

noncomputable def basisFinset : Finset (ℤ × ℤ) := {((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))}

theorem closure_basisFinset :
    AddSubgroup.closure ((basisFinset : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro p
  set S := AddSubgroup.closure ((basisFinset : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) with hS
  have h1 : ((1 : ℤ), (0 : ℤ)) ∈ S :=
    AddSubgroup.subset_closure (by simp [basisFinset])
  have h2 : ((0 : ℤ), (1 : ℤ)) ∈ S :=
    AddSubgroup.subset_closure (by simp [basisFinset])

  have key1 : ∀ n : ℤ, ((n : ℤ), (0 : ℤ)) ∈ S := by
    intro n
    induction n using Int.induction_on with
    | zero => exact zero_mem S
    | succ k ih =>
      have he : (((k : ℤ) + 1, (0 : ℤ)) : ℤ × ℤ) = ((k : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)) := by
        rw [Prod.mk_add_mk, add_zero]
      rw [he]
      exact add_mem ih h1
    | pred k ih =>
      have he : ((-(k : ℤ) - 1, (0 : ℤ)) : ℤ × ℤ) = (-(k : ℤ), (0 : ℤ)) - ((1 : ℤ), (0 : ℤ)) := by
        rw [Prod.mk_sub_mk, sub_zero]
      rw [he]
      exact sub_mem ih h1

  have key2 : ∀ n : ℤ, ((0 : ℤ), (n : ℤ)) ∈ S := by
    intro n
    induction n using Int.induction_on with
    | zero => exact zero_mem S
    | succ k ih =>
      have he : (((0 : ℤ), (k : ℤ) + 1) : ℤ × ℤ) = ((0 : ℤ), (k : ℤ)) + ((0 : ℤ), (1 : ℤ)) := by
        rw [Prod.mk_add_mk, add_zero]
      rw [he]
      exact add_mem ih h2
    | pred k ih =>
      have he : (((0 : ℤ), -(k : ℤ) - 1) : ℤ × ℤ) = ((0 : ℤ), -(k : ℤ)) - ((0 : ℤ), (1 : ℤ)) := by
        rw [Prod.mk_sub_mk, sub_zero]
      rw [he]
      exact sub_mem ih h2
  have hp : p = (p.1, (0 : ℤ)) + ((0 : ℤ), p.2) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  rw [hp]
  exact add_mem (key1 p.1) (key2 p.2)

theorem gate_denominator_two_load_bearing :
    eigenbasisHom ((1 : ℤ), (0 : ℤ)) ∉ intCastHom₂.range := by
  intro hmem
  obtain ⟨⟨a, b⟩, hab⟩ := AddMonoidHom.mem_range.mp hmem
  have h1 : ((a : ℚ), (b : ℚ)) = ((((1 : ℤ) : ℚ) + ((0 : ℤ) : ℚ)) / 2,
      (((1 : ℤ) : ℚ) - ((0 : ℤ) : ℚ)) / 2) := hab
  rw [Prod.mk.injEq] at h1
  have ha : (a : ℚ) = 1 / 2 := by
    rw [h1.1]
    norm_num
  have h2a : ((2 * a : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    push_cast
    rw [ha]
    ring
  have : (2 * a : ℤ) = 1 := Int.cast_injective h2a
  omega

theorem eigenbasis_uniform_denominator :
    ∀ a ∈ basisFinset, ∃ n : ℕ, n ≠ 0 ∧ n • eigenbasisHom a ∈ intCastHom₂.range := by
  intro a _
  refine ⟨2, two_ne_zero, ?_⟩
  refine AddMonoidHom.mem_range.mpr ⟨(a.1 + a.2, a.1 - a.2), ?_⟩
  rw [two_nsmul]
  show (((a.1 + a.2 : ℤ) : ℚ), ((a.1 - a.2 : ℤ) : ℚ))
    = (((a.1 : ℚ) + (a.2 : ℚ)) / 2, ((a.1 : ℚ) - (a.2 : ℚ)) / 2)
      + (((a.1 : ℚ) + (a.2 : ℚ)) / 2, ((a.1 : ℚ) - (a.2 : ℚ)) / 2)
  rw [Prod.mk_add_mk, Prod.mk.injEq]
  push_cast
  exact ⟨by ring, by ring⟩

theorem eigenbasis_reverse_denominator :
    ∀ b ∈ basisFinset, ∃ n : ℕ, n ≠ 0 ∧ n • intCastHom₂ b ∈ eigenbasisHom.range := by
  intro b _
  refine ⟨1, one_ne_zero, ?_⟩
  refine AddMonoidHom.mem_range.mpr ⟨(b.1 + b.2, b.1 - b.2), ?_⟩
  rw [one_nsmul]
  show ((((b.1 + b.2 : ℤ) : ℚ) + ((b.1 - b.2 : ℤ) : ℚ)) / 2,
        (((b.1 + b.2 : ℤ) : ℚ) - ((b.1 - b.2 : ℤ) : ℚ)) / 2)
    = ((b.1 : ℚ), (b.2 : ℚ))
  rw [Prod.mk.injEq]
  push_cast
  exact ⟨by ring, by ring⟩

theorem eigenbasis_intertwines_derive :
    ∀ a, ratDiagPair.derive (eigenbasisHom a) = eigenbasisHom (intSwapPair.derive a) := by
  intro p
  show ((0 : ℚ), -(2 * (((p.1 : ℚ) - (p.2 : ℚ)) / 2)))
    = ((((p.2 - p.1 : ℤ) : ℚ) + ((p.1 - p.2 : ℤ) : ℚ)) / 2,
       (((p.2 - p.1 : ℤ) : ℚ) - ((p.1 - p.2 : ℤ) : ℚ)) / 2)
  rw [Prod.mk.injEq]
  push_cast
  exact ⟨by ring, by ring⟩

theorem eigenbasis_intertwines_norm :
    ∀ a, ratDiagPair.norm (eigenbasisHom a) = eigenbasisHom (intSwapPair.norm a) := by
  intro p
  show ((2 * (((p.1 : ℚ) + (p.2 : ℚ)) / 2)), (0 : ℚ))
    = ((((p.1 + p.2 : ℤ) : ℚ) + ((p.1 + p.2 : ℤ) : ℚ)) / 2,
       (((p.1 + p.2 : ℤ) : ℚ) - ((p.1 + p.2 : ℤ) : ℚ)) / 2)
  rw [Prod.mk.injEq]
  push_cast
  exact ⟨by ring, by ring⟩

theorem intCast_intertwines_derive :
    ∀ b, ratDiagPair.derive (intCastHom₂ b) = intCastHom₂ (intDiagPair.derive b) := by
  intro p
  show ((0 : ℚ), -(2 * (p.2 : ℚ))) = (((0 : ℤ) : ℚ), ((-(2 * p.2) : ℤ) : ℚ))
  rw [Prod.mk.injEq]
  push_cast
  exact ⟨by ring, by ring⟩

theorem intCast_intertwines_norm :
    ∀ b, ratDiagPair.norm (intCastHom₂ b) = intCastHom₂ (intDiagPair.norm b) := by
  intro p
  show ((2 * (p.1 : ℚ)), (0 : ℚ)) = (((2 * p.1 : ℤ) : ℚ), ((0 : ℤ) : ℚ))
  rw [Prod.mk.injEq]
  push_cast
  exact ⟨by ring, by ring⟩

theorem gate_denominator_clearing_fires :
    ∃ f : ℤ × ℤ →+ ℤ × ℤ, Function.Injective f
      ∧ (∀ a, intDiagPair.derive (f a) = f (intSwapPair.derive a))
      ∧ (∀ a, intDiagPair.norm (f a) = f (intSwapPair.norm a))
      ∧ Finite ((ℤ × ℤ) ⧸ f.range) :=
  exists_intertwining_injective_of_rational_equiv intSwapPair intDiagPair ratDiagPair
    eigenbasisHom intCastHom₂ eigenbasisHom_injective intCastHom₂_injective
    eigenbasis_intertwines_derive eigenbasis_intertwines_norm
    intCast_intertwines_derive intCast_intertwines_norm
    basisFinset closure_basisFinset eigenbasis_uniform_denominator
    basisFinset closure_basisFinset eigenbasis_reverse_denominator

theorem gate_cleared_map_cokernel_nontrivial
    (hmem : ∀ a : ℤ × ℤ, (2 : ℕ) • eigenbasisHom a ∈ intCastHom₂.range) :
    ((1 : ℤ), (0 : ℤ)) ∉ (clearDenominator eigenbasisHom intCastHom₂
      intCastHom₂_injective 2 hmem).range := by
  intro hr
  obtain ⟨⟨x, y⟩, hxy⟩ := AddMonoidHom.mem_range.mp hr
  have hval : clearDenominator eigenbasisHom intCastHom₂ intCastHom₂_injective 2 hmem (x, y)
      = (x + y, x - y) := by
    refine clearDenominator_eq_of_ιB_eq eigenbasisHom intCastHom₂ intCastHom₂_injective
      2 hmem ?_
    rw [two_nsmul]
    show (((x + y : ℤ) : ℚ), ((x - y : ℤ) : ℚ))
      = ((((x : ℚ) + (y : ℚ)) / 2), (((x : ℚ) - (y : ℚ)) / 2))
        + ((((x : ℚ) + (y : ℚ)) / 2), (((x : ℚ) - (y : ℚ)) / 2))
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    push_cast
    exact ⟨by ring, by ring⟩
  rw [hval, Prod.mk.injEq] at hxy
  omega

theorem gate_reverse_denominator_load_bearing :
    (∀ n : ℕ, n ≠ 0 →
        n • intCastHom₂ ((0 : ℤ), (1 : ℤ)) ∉ (intCastHom₂.comp (AddMonoidHom.inl ℤ ℤ)).range)
      ∧ Infinite ((ℤ × ℤ) ⧸ (AddMonoidHom.inl ℤ ℤ).range) := by
  constructor
  · intro n hn hmem
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hmem

    have h2 := congrArg (⇑(AddMonoidHom.snd ℚ ℚ)) ha
    rw [map_nsmul] at h2
    have h3 : ((0 : ℤ) : ℚ) = n • ((1 : ℤ) : ℚ) := h2
    rw [nsmul_eq_mul] at h3
    push_cast at h3
    have h4 : n * 1 = 0 := by exact_mod_cast h3.symm
    omega
  ·
    have hker : (AddMonoidHom.inl ℤ ℤ).range = (AddMonoidHom.snd ℤ ℤ).ker := by
      ext x
      simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, AddMonoidHom.inl_apply,
        AddMonoidHom.coe_snd, Prod.ext_iff]
      constructor
      · rintro ⟨a, _, hc⟩
        exact hc.symm
      · intro h
        exact ⟨x.1, rfl, h.symm⟩
    rw [hker]
    exact Infinite.of_surjective _
      (QuotientAddGroup.quotientKerEquivOfSurjective (AddMonoidHom.snd ℤ ℤ)
        (fun c => ⟨(0, c), rfl⟩)).surjective

theorem tateCard₀_intSwapPair : intSwapPair.tateCard₀ = 1 := by
  have hle : intSwapPair.derive.ker ≤ intSwapPair.norm.range := by
    rintro ⟨a, b⟩ hx
    rw [AddMonoidHom.mem_ker] at hx
    have h1 : ((b - a, a - b) : ℤ × ℤ) = (0, 0) := hx
    rw [Prod.mk.injEq] at h1
    refine AddMonoidHom.mem_range.mpr ⟨((a : ℤ), (0 : ℤ)), ?_⟩
    show ((a + 0 : ℤ), (a + 0 : ℤ)) = ((a : ℤ), (b : ℤ))
    rw [Prod.mk.injEq]
    constructor <;> omega
  rw [HerbrandPair.tateCard₀, Nat.card_eq_one_iff_exists]
  refine ⟨QuotientAddGroup.mk 0, fun y => QuotientAddGroup.induction_on y fun x => ?_⟩
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have hcast : ((-x + 0 : intSwapPair.derive.ker) : ℤ × ℤ) = -(x : ℤ × ℤ) := by
    push_cast
    rw [add_zero]
  rw [hcast]
  exact hle (neg_mem x.2)

theorem tateCard₁_intSwapPair : intSwapPair.tateCard₁ = 1 := by
  have hle : intSwapPair.norm.ker ≤ intSwapPair.derive.range := by
    rintro ⟨a, b⟩ hx
    rw [AddMonoidHom.mem_ker] at hx
    have h1 : ((a + b, a + b) : ℤ × ℤ) = (0, 0) := hx
    rw [Prod.mk.injEq] at h1
    refine AddMonoidHom.mem_range.mpr ⟨((0 : ℤ), (a : ℤ)), ?_⟩
    show ((a - 0 : ℤ), (0 - a : ℤ)) = ((a : ℤ), (b : ℤ))
    rw [Prod.mk.injEq]
    constructor <;> omega
  rw [HerbrandPair.tateCard₁, Nat.card_eq_one_iff_exists]
  refine ⟨QuotientAddGroup.mk 0, fun y => QuotientAddGroup.induction_on y fun x => ?_⟩
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have hcast : ((-x + 0 : intSwapPair.norm.ker) : ℤ × ℤ) = -(x : ℤ × ℤ) := by
    push_cast
    rw [add_zero]
  rw [hcast]
  exact hle (neg_mem x.2)

theorem gate_eigenbasis_tateCard_cancel :
    intDiagPair.tateCard₀ = intDiagPair.tateCard₁ := by
  have hcross : intSwapPair.tateCard₀ * intDiagPair.tateCard₁
      = intDiagPair.tateCard₀ * intSwapPair.tateCard₁ :=
    tateCard_cross_eq_of_rational_equiv intSwapPair intDiagPair ratDiagPair
      eigenbasisHom intCastHom₂ eigenbasisHom_injective intCastHom₂_injective
      eigenbasis_intertwines_derive eigenbasis_intertwines_norm
      intCast_intertwines_derive intCast_intertwines_norm
      basisFinset closure_basisFinset eigenbasis_uniform_denominator
      basisFinset closure_basisFinset eigenbasis_reverse_denominator
  rw [tateCard₀_intSwapPair, tateCard₁_intSwapPair, one_mul, mul_one] at hcross
  exact hcross.symm

theorem gate_denominator_clearing_refl :
    ∃ f : ℤ × ℤ →+ ℤ × ℤ, Function.Injective f
      ∧ (∀ a, intDiagPair.derive (f a) = f (intDiagPair.derive a))
      ∧ (∀ a, intDiagPair.norm (f a) = f (intDiagPair.norm a))
      ∧ Finite ((ℤ × ℤ) ⧸ f.range) := by
  have hrefl : ∀ b ∈ basisFinset, ∃ n : ℕ, n ≠ 0 ∧ n • intCastHom₂ b ∈ intCastHom₂.range :=
    fun b _ => ⟨1, one_ne_zero, AddMonoidHom.mem_range.mpr ⟨b, by rw [one_nsmul]⟩⟩
  exact exists_intertwining_injective_of_rational_equiv intDiagPair intDiagPair ratDiagPair
    intCastHom₂ intCastHom₂ intCastHom₂_injective intCastHom₂_injective
    intCast_intertwines_derive intCast_intertwines_norm
    intCast_intertwines_derive intCast_intertwines_norm
    basisFinset closure_basisFinset hrefl
    basisFinset closure_basisFinset hrefl

end Gates
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

end Fold_DenominatorClearing
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

section Fold_FGTateFinite

set_option autoImplicit false

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace FGTateFinite
p2m_open "M4aHerbrand"

open M4aLocalCFT Finset

section Helpers

variable {A : Type*} [AddCommGroup A] (σ : AddAut A) {n : ℕ} (h : σ ^ n = 1)

theorem norm_eq_nsmul_of_mem_ker_derive (a : A) (ha : a ∈ (HerbrandPair.ofAddAut σ n h).derive.ker) :
    (HerbrandPair.ofAddAut σ n h).norm a = n • a := by
  have hfix : ∀ i, (σ ^ i) a = a := by
    have hσa : σ a = a := by
      have := AddMonoidHom.mem_ker.mp ha; rwa [HerbrandPair.ofAddAut_derive_apply, sub_eq_zero] at this
    intro i; induction i with
    | zero => simp
    | succ k ih => rw [pow_succ', AddAut.mul_apply', ih, hσa]
  rw [HerbrandPair.ofAddAut_norm_apply]
  calc ∑ i ∈ range n, (σ ^ i) a = ∑ _i ∈ range n, a :=
        Finset.sum_congr rfl (fun i _ => hfix i)
    _ = n • a := by rw [Finset.sum_const, card_range]

theorem pow_apply_sub_mem_range_derive (a : A) (i : ℕ) :
    (σ ^ i) a - a ∈ (HerbrandPair.ofAddAut σ n h).derive.range := by
  induction i with
  | zero => simp
  | succ k ih =>
    have hstep : (σ ^ (k + 1)) a - a = (σ ((σ ^ k) a) - (σ ^ k) a) + ((σ ^ k) a - a) := by
      rw [pow_succ', AddAut.mul_apply']; abel
    rw [hstep]
    exact add_mem ⟨(σ ^ k) a, HerbrandPair.ofAddAut_derive_apply σ n h _⟩ ih

theorem nsmul_mem_range_derive_of_mem_ker_norm (a : A)
    (ha : a ∈ (HerbrandPair.ofAddAut σ n h).norm.ker) :
    n • a ∈ (HerbrandPair.ofAddAut σ n h).derive.range := by
  have hid : n • a = ∑ i ∈ range n, (a - (σ ^ i) a) + (HerbrandPair.ofAddAut σ n h).norm a := by
    rw [HerbrandPair.ofAddAut_norm_apply, ← Finset.sum_add_distrib]
    simp [Finset.sum_const, card_range]
  rw [hid, AddMonoidHom.mem_ker.mp ha, add_zero]
  refine sum_mem fun i _ => ?_
  rw [show a - (σ ^ i) a = -((σ ^ i) a - a) from (neg_sub _ _).symm]
  exact neg_mem (pow_apply_sub_mem_range_derive σ h a i)

variable [AddGroup.FG A]

scoped instance instFGAddSubgroup (H : AddSubgroup A) : AddGroup.FG ↥H := by
  have hfin : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr ‹_›
  have hN : (H.toIntSubmodule : Submodule ℤ A).FG := IsNoetherian.noetherian _
  rw [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at hN
  exact (AddGroup.fg_iff_addSubgroup_fg H).mpr hN

omit [AddGroup.FG A] in

theorem isTorsion_tateQuot₀ (hn : 0 < n) :
    AddMonoid.IsTorsion (↥(HerbrandPair.ofAddAut σ n h).derive.ker ⧸
      ((HerbrandPair.ofAddAut σ n h).norm.range.addSubgroupOf (HerbrandPair.ofAddAut σ n h).derive.ker)) := by
  intro q
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  induction q using QuotientAddGroup.induction_on with
  | H a =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    show (n • a : A) ∈ (HerbrandPair.ofAddAut σ n h).norm.range
    exact ⟨a.1, norm_eq_nsmul_of_mem_ker_derive σ h a.1 a.2⟩

omit [AddGroup.FG A] in

theorem isTorsion_tateQuot₁ (hn : 0 < n) :
    AddMonoid.IsTorsion (↥(HerbrandPair.ofAddAut σ n h).norm.ker ⧸
      ((HerbrandPair.ofAddAut σ n h).derive.range.addSubgroupOf (HerbrandPair.ofAddAut σ n h).norm.ker)) := by
  intro q
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  induction q using QuotientAddGroup.induction_on with
  | H a =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    show (n • a : A) ∈ (HerbrandPair.ofAddAut σ n h).derive.range
    exact nsmul_mem_range_derive_of_mem_ker_norm σ h a.1 a.2

end Helpers
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

theorem tateCard_ne_zero_of_fg {A : Type*} [AddCommGroup A] [AddGroup.FG A] (σ : AddAut A) {n : ℕ} (hn : 0 < n)
    (h : σ ^ n = 1) :
    (HerbrandPair.ofAddAut σ n h).tateCard₀ ≠ 0 ∧ (HerbrandPair.ofAddAut σ n h).tateCard₁ ≠ 0 := by
  have hfin : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr ‹_›
  refine ⟨?_, ?_⟩
  ·
    have : Finite (↥(HerbrandPair.ofAddAut σ n h).derive.ker ⧸
        ((HerbrandPair.ofAddAut σ n h).norm.range.addSubgroupOf (HerbrandPair.ofAddAut σ n h).derive.ker)) :=
      AddCommGroup.finite_of_fg_torsion
        (G := ↥(HerbrandPair.ofAddAut σ n h).derive.ker ⧸
          ((HerbrandPair.ofAddAut σ n h).norm.range.addSubgroupOf (HerbrandPair.ofAddAut σ n h).derive.ker))
        (isTorsion_tateQuot₀ σ h hn)
    exact Nat.card_pos.ne'
  ·
    have : Finite (↥(HerbrandPair.ofAddAut σ n h).norm.ker ⧸
        ((HerbrandPair.ofAddAut σ n h).derive.range.addSubgroupOf (HerbrandPair.ofAddAut σ n h).norm.ker)) :=
      AddCommGroup.finite_of_fg_torsion
        (G := ↥(HerbrandPair.ofAddAut σ n h).norm.ker ⧸
          ((HerbrandPair.ofAddAut σ n h).derive.range.addSubgroupOf (HerbrandPair.ofAddAut σ n h).norm.ker))
        (isTorsion_tateQuot₁ σ h hn)
    exact Nat.card_pos.ne'

end M4aHerbrand.FGTateFinite
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule"

section Battery
open M4aHerbrand.FGTateFinite
#print axioms norm_eq_nsmul_of_mem_ker_derive
#print axioms pow_apply_sub_mem_range_derive
#print axioms nsmul_mem_range_derive_of_mem_ker_norm
#print axioms instFGAddSubgroup
#print axioms isTorsion_tateQuot₀
#print axioms isTorsion_tateQuot₁
#print axioms tateCard_ne_zero_of_fg
end Battery
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

section ed19Prints
open M4aHerbrand.FGTateFinite
set_option pp.deepTerms true in
set_option pp.funBinderTypes true in
#check @tateCard_ne_zero_of_fg
end ed19Prints
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

end Fold_FGTateFinite
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

section Fold_FirstInequalityAssembly

open Finset

namespace M4aLocalCFT

namespace FirstInequality

open HerbrandPair LocalUnitsCohomology

theorem mul_eq_mul_of_hexagon {u₀ u₁ i₀ i₁ c₀ c₁ N n : ℕ}
    (hhex : u₀ * c₀ * i₁ = i₀ * u₁ * c₁)
    (hI : i₀ = N * i₁)
    (hU : u₀ * n = N * u₁) :
    u₀ * i₁ * c₀ = u₀ * i₁ * (n * c₁) := by
  calc u₀ * i₁ * c₀ = u₀ * c₀ * i₁ := by ring
    _ = i₀ * u₁ * c₁ := hhex
    _ = N * u₁ * (i₁ * c₁) := by rw [hI]; ring
    _ = u₀ * n * (i₁ * c₁) := by rw [hU]
    _ = u₀ * i₁ * (n * c₁) := by ring

theorem gate_cancellation_load_bearing :
    ∃ u₀ i₁ c₀ c₁ n : ℕ,
      u₀ * i₁ * c₀ = u₀ * i₁ * (n * c₁) ∧ c₀ ≠ n * c₁ := by
  exact ⟨0, 1, 5, 1, 2, by norm_num, by decide⟩

variable {U I C : Type} [AddCommGroup U] [AddCommGroup I] [AddCommGroup C]

theorem firstInequality_tateCard_mul (T : HerbrandTriple U I C) {N n : ℕ}
    (hI : T.Q.tateCard₀ = N * T.Q.tateCard₁)
    (hU : T.P.tateCard₀ * n = N * T.P.tateCard₁) :
    T.P.tateCard₀ * T.Q.tateCard₁ * T.R.tateCard₀
      = T.P.tateCard₀ * T.Q.tateCard₁ * (n * T.R.tateCard₁) :=
  mul_eq_mul_of_hexagon T.tateCard_mul hI hU

theorem firstInequality_tateCard_eq (T : HerbrandTriple U I C) {N n : ℕ}
    (hI : T.Q.tateCard₀ = N * T.Q.tateCard₁)
    (hU : T.P.tateCard₀ * n = N * T.P.tateCard₁)
    (hpos : T.P.tateCard₀ * T.Q.tateCard₁ ≠ 0) :
    T.R.tateCard₀ = n * T.R.tateCard₁ :=
  Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos)
    (firstInequality_tateCard_mul T hI hU)

theorem firstInequality_dvd (T : HerbrandTriple U I C) {N n : ℕ}
    (hI : T.Q.tateCard₀ = N * T.Q.tateCard₁)
    (hU : T.P.tateCard₀ * n = N * T.P.tateCard₁)
    (hpos : T.P.tateCard₀ * T.Q.tateCard₁ ≠ 0) :
    n ∣ T.R.tateCard₀ :=
  ⟨T.R.tateCard₁, firstInequality_tateCard_eq T hI hU hpos⟩

theorem firstInequality_le (T : HerbrandTriple U I C) {N n : ℕ}
    (hI : T.Q.tateCard₀ = N * T.Q.tateCard₁)
    (hU : T.P.tateCard₀ * n = N * T.P.tateCard₁)
    (hpos : T.P.tateCard₀ * T.Q.tateCard₁ ≠ 0)
    (hC : T.R.tateCard₁ ≠ 0) :
    n ≤ T.R.tateCard₀ := by
  rw [firstInequality_tateCard_eq T hI hU hpos]
  exact Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hC)

theorem firstInequality_le_or_eq_zero (T : HerbrandTriple U I C) {N n : ℕ}
    (hI : T.Q.tateCard₀ = N * T.Q.tateCard₁)
    (hU : T.P.tateCard₀ * n = N * T.P.tateCard₁)
    (hpos : T.P.tateCard₀ * T.Q.tateCard₁ ≠ 0) :
    n ≤ T.R.tateCard₀ ∨ T.R.tateCard₀ = 0 := by
  rcases Nat.eq_zero_or_pos T.R.tateCard₁ with hC | hC
  · right
    rw [firstInequality_tateCard_eq T hI hU hpos, hC, mul_zero]
  · exact Or.inl (firstInequality_le T hI hU hpos hC.ne')

theorem firstInequality_index_eq_of_le (T : HerbrandTriple U I C) {N n : ℕ}
    (hI : T.Q.tateCard₀ = N * T.Q.tateCard₁)
    (hU : T.P.tateCard₀ * n = N * T.P.tateCard₁)
    (hpos : T.P.tateCard₀ * T.Q.tateCard₁ ≠ 0)
    (hC : T.R.tateCard₁ ≠ 0)
    (hsecond : T.R.tateCard₀ ≤ n) :
    T.R.tateCard₀ = n :=
  le_antisymm hsecond (firstInequality_le T hI hU hpos hC)

private noncomputable def quadraticSplitTriple : HerbrandTriple ℤ (ℤ × ℤ) ℤ :=
  prodTriple (intCyclicPair 2) (intCyclicPair 2)

theorem gate_firstInequality_fires_at_quadratic :
    quadraticSplitTriple.R.tateCard₀ = 2 * quadraticSplitTriple.R.tateCard₁ ∧
      quadraticSplitTriple.R.tateCard₀ = 2 ∧ (2 : ℕ) ≠ 1 := by
  have hU₀ : (intCyclicPair 2).tateCard₀ = 2 := tateCard₀_intCyclicPair (by norm_num)
  have hU₁ : (intCyclicPair 2).tateCard₁ = 1 := tateCard₁_intCyclicPair (by norm_num)
  have hQ₀ : quadraticSplitTriple.Q.tateCard₀ = 4 := by
    show ((intCyclicPair 2).prod (intCyclicPair 2)).tateCard₀ = 4
    rw [tateCard₀_prod, hU₀]
  have hQ₁ : quadraticSplitTriple.Q.tateCard₁ = 1 := by
    show ((intCyclicPair 2).prod (intCyclicPair 2)).tateCard₁ = 1
    rw [tateCard₁_prod, hU₁]
  refine ⟨?_, ?_, by norm_num⟩
  · refine firstInequality_tateCard_eq quadraticSplitTriple (N := 4) ?_ ?_ ?_
    · rw [hQ₀, hQ₁]
    · show (intCyclicPair 2).tateCard₀ * 2 = 4 * (intCyclicPair 2).tateCard₁
      rw [hU₀, hU₁]
    · show (intCyclicPair 2).tateCard₀ * _ ≠ 0
      rw [hU₀, hQ₁]
      norm_num
  · exact hU₀

theorem gate_firstInequality_content :
    (2 : ℕ) ≤ quadraticSplitTriple.R.tateCard₀ ∧
      1 < quadraticSplitTriple.R.tateCard₀ := by
  have h := gate_firstInequality_fires_at_quadratic
  constructor
  · rw [h.2.1]
  · rw [h.2.1]; norm_num

theorem gate_le_form_consumes_finiteness :
    ∃ c₀ c₁ n : ℕ, c₀ = n * c₁ ∧ ¬ n ≤ c₀ := by
  exact ⟨0, 0, 2, by norm_num, by norm_num⟩

theorem gate_firstInequality_degenerate (T : HerbrandTriple U I C) {N : ℕ}
    (hI : T.Q.tateCard₀ = N * T.Q.tateCard₁)
    (hU : T.P.tateCard₀ * 1 = N * T.P.tateCard₁)
    (hpos : T.P.tateCard₀ * T.Q.tateCard₁ ≠ 0) :
    T.R.tateCard₀ = T.R.tateCard₁ := by
  have h := firstInequality_tateCard_eq T hI hU hpos
  rwa [one_mul] at h

end FirstInequality
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

end Fold_FirstInequalityAssembly
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

section Fold_FirstInequalityShape

set_option autoImplicit false

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace FirstInequalityShape
p2m_open "M4aHerbrand"

open M4aLocalCFT M4aLocalCFT.HerbrandPair

section Equivariant

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  (σ : AddAut A) (τ : AddAut B) (f : A →+ B) (hf : ∀ a, f (σ a) = τ (f a))

include hf in
theorem map_pow_apply (i : ℕ) (a : A) : f ((σ ^ i) a) = (τ ^ i) (f a) := by
  induction i generalizing a with
  | zero => rfl
  | succ i ih => rw [pow_succ, AddAut.mul_apply', ih, hf, pow_succ, AddAut.mul_apply']

include hf in

theorem derive_comm {n : ℕ} (hσ : σ ^ n = 1) (hτ : τ ^ n = 1) (a : A) :
    (ofAddAut τ n hτ).derive (f a) = f ((ofAddAut σ n hσ).derive a) := by
  rw [ofAddAut_derive_apply, ofAddAut_derive_apply, map_sub, hf]

include hf in

theorem norm_comm {n : ℕ} (hσ : σ ^ n = 1) (hτ : τ ^ n = 1) (a : A) :
    (ofAddAut τ n hτ).norm (f a) = f ((ofAddAut σ n hσ).norm a) := by
  rw [ofAddAut_norm_apply, ofAddAut_norm_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => (map_pow_apply σ τ f hf i a).symm

include hf in

theorem range_stable : ∀ b ∈ f.range, τ b ∈ f.range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨σ a, hf a⟩

include hf in
theorem range_stable_symm : ∀ b ∈ f.range, τ.symm b ∈ f.range := by
  rintro _ ⟨a, rfl⟩
  refine ⟨σ.symm a, τ.injective ?_⟩
  rw [τ.apply_symm_apply, ← hf, σ.apply_symm_apply]

end Equivariant
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

section Quot

variable {A : Type*} [AddCommGroup A] (σ : AddAut A) (H : AddSubgroup A)

theorem map_eq_of_stable (h : ∀ a ∈ H, σ a ∈ H) (h' : ∀ a ∈ H, σ.symm a ∈ H) :
    H.map σ.toAddMonoidHom = H := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  · intro a ha
    exact ⟨σ.symm a, h' a ha, σ.apply_symm_apply a⟩

def quotAut (h : ∀ a ∈ H, σ a ∈ H) (h' : ∀ a ∈ H, σ.symm a ∈ H) : AddAut (A ⧸ H) :=
  QuotientAddGroup.congr H H σ (map_eq_of_stable σ H h h')

theorem quotAut_mk (h : ∀ a ∈ H, σ a ∈ H) (h' : ∀ a ∈ H, σ.symm a ∈ H) (a : A) :
    quotAut σ H h h' (QuotientAddGroup.mk a) = QuotientAddGroup.mk (σ a) :=
  rfl

theorem mk'_quotAut (h : ∀ a ∈ H, σ a ∈ H) (h' : ∀ a ∈ H, σ.symm a ∈ H) (a : A) :
    QuotientAddGroup.mk' H (σ a) = quotAut σ H h h' (QuotientAddGroup.mk' H a) :=
  (quotAut_mk σ H h h' a).symm

theorem quotAut_pow_mk (h : ∀ a ∈ H, σ a ∈ H) (h' : ∀ a ∈ H, σ.symm a ∈ H) (i : ℕ) (a : A) :
    (quotAut σ H h h' ^ i) (QuotientAddGroup.mk a) = QuotientAddGroup.mk ((σ ^ i) a) :=
  (map_pow_apply σ (quotAut σ H h h') (QuotientAddGroup.mk' H) (mk'_quotAut σ H h h') i a).symm

theorem quotAut_pow_eq_one (h : ∀ a ∈ H, σ a ∈ H) (h' : ∀ a ∈ H, σ.symm a ∈ H) {n : ℕ}
    (hσ : σ ^ n = 1) : quotAut σ H h h' ^ n = 1 := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H a => rw [quotAut_pow_mk, hσ]; rfl

end Quot
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

section Hexagon

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

theorem tateCard₀_quot_ne_zero (S : HerbrandTriple A B C) (hP : S.P.tateCard₁ ≠ 0)
    (hQ : S.Q.tateCard₀ ≠ 0) : S.R.tateCard₀ ≠ 0 := by
  haveI : Finite (S.P.norm.ker ⧸ S.P.derive.range.addSubgroupOf S.P.norm.ker) :=
    Nat.finite_of_card_ne_zero hP
  haveI : Finite (S.Q.derive.ker ⧸ S.Q.norm.range.addSubgroupOf S.Q.derive.ker) :=
    Nat.finite_of_card_ne_zero hQ
  have key := nat_card_eq_card_range_mul_card_ker S.connecting
  rw [← S.exact_at_quot] at key
  show Nat.card (S.R.derive.ker ⧸ S.R.norm.range.addSubgroupOf S.R.derive.ker) ≠ 0
  rw [key]
  refine mul_ne_zero ?_ ?_
  · exact Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩
  · exact Nat.card_ne_zero.mpr ⟨⟨0⟩, Finite.of_surjective _ S.inducedπ.rangeRestrict_surjective⟩

theorem tateCard₁_quot_ne_zero (T : HerbrandTriple A B C) (hP : T.P.tateCard₀ ≠ 0)
    (hQ : T.Q.tateCard₁ ≠ 0) : T.R.tateCard₁ ≠ 0 :=
  tateCard₀_quot_ne_zero T.swap hP hQ

theorem firstInequality_tateCard_eq' (T : HerbrandTriple A B C) {N n : ℕ}
    (hI : T.Q.tateCard₀ = N * T.Q.tateCard₁)
    (hU : T.P.tateCard₀ * n = N * T.P.tateCard₁)
    (hpos : T.P.tateCard₀ * T.Q.tateCard₁ ≠ 0) :
    T.R.tateCard₀ = n * T.R.tateCard₁ :=
  Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) (FirstInequality.mul_eq_mul_of_hexagon T.tateCard_mul hI hU)

end Hexagon
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

section Shape

variable {U I C : Type*} [AddCommGroup U] [AddCommGroup I] [AddCommGroup C]

theorem tateCard₀_eq_of_shape (σU : AddAut U) (σI : AddAut I) (σC : AddAut C) {n : ℕ}
    (hU1 : σU ^ n = 1) (hI1 : σI ^ n = 1) (hC1 : σC ^ n = 1)
    (κ : U →+ I) (φ : I →+ C)
    (hκ : Function.Injective κ) (hκσ : ∀ u, κ (σU u) = σI (κ u)) (hφσ : ∀ i, φ (σI i) = σC (φ i))
    (hex : κ.range = φ.ker) (hfin : Finite (C ⧸ φ.range)) {N : ℕ}
    (hI : (ofAddAut σI n hI1).tateCard₀ = N * (ofAddAut σI n hI1).tateCard₁)
    (hU : (ofAddAut σU n hU1).tateCard₀ * n = N * (ofAddAut σU n hU1).tateCard₁)
    (hpos : (ofAddAut σU n hU1).tateCard₀ * (ofAddAut σI n hI1).tateCard₁ ≠ 0) :
    (ofAddAut σC n hC1).tateCard₀ = n * (ofAddAut σC n hC1).tateCard₁ := by

  have hs := range_stable σU σI κ hκσ
  have hs' := range_stable_symm σU σI κ hκσ
  let σQ : AddAut (I ⧸ κ.range) := quotAut σI κ.range hs hs'
  have hQ1 : σQ ^ n = 1 := quotAut_pow_eq_one σI κ.range hs hs' hI1
  have hmkσ : ∀ i, QuotientAddGroup.mk' κ.range (σI i) = σQ (QuotientAddGroup.mk' κ.range i) :=
    mk'_quotAut σI κ.range hs hs'

  let T₁ : HerbrandTriple U I (I ⧸ κ.range) :=
    { P := ofAddAut σU n hU1
      Q := ofAddAut σI n hI1
      R := ofAddAut σQ n hQ1
      ι := κ
      π := QuotientAddGroup.mk' κ.range
      ι_injective := hκ
      π_surjective := QuotientAddGroup.mk'_surjective _
      exact := (QuotientAddGroup.ker_mk' κ.range).symm
      derive_ι := derive_comm σU σI κ hκσ hU1 hI1
      norm_ι := norm_comm σU σI κ hκσ hU1 hI1
      derive_π := derive_comm σI σQ _ hmkσ hI1 hQ1
      norm_π := norm_comm σI σQ _ hmkσ hI1 hQ1 }
  have h1 : T₁.R.tateCard₀ = n * T₁.R.tateCard₁ := firstInequality_tateCard_eq' T₁ hI hU hpos
  have hR1 : T₁.R.tateCard₁ ≠ 0 :=
    tateCard₁_quot_ne_zero T₁ (left_ne_zero_of_mul hpos) (right_ne_zero_of_mul hpos)

  have hle : κ.range ≤ φ.ker := hex.le
  let φ' : I ⧸ κ.range →+ C := QuotientAddGroup.lift κ.range φ hle
  have hφ'mk : ∀ i, φ' (QuotientAddGroup.mk i) = φ i := fun i => QuotientAddGroup.lift_mk' κ.range hle i
  have hφ'inj : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | H i =>
      rw [hφ'mk] at hx
      have hi : i ∈ κ.range := by rw [hex]; exact hx
      exact (QuotientAddGroup.eq_zero_iff i).mpr hi
  have hφ'range : φ'.range = φ.range := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientAddGroup.induction_on with
      | H i => exact ⟨i, (hφ'mk i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨QuotientAddGroup.mk i, hφ'mk i⟩
  have hφ'σ : ∀ x, φ' (σQ x) = σC (φ' x) := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H i =>
      show φ' (quotAut σI κ.range hs hs' (QuotientAddGroup.mk i)) = σC (φ' (QuotientAddGroup.mk i))
      rw [quotAut_mk, hφ'mk, hφ'mk, hφσ]

  have ht := range_stable σI σC φ hφσ
  have ht' := range_stable_symm σI σC φ hφσ
  let σR : AddAut (C ⧸ φ.range) := quotAut σC φ.range ht ht'
  have hRn : σR ^ n = 1 := quotAut_pow_eq_one σC φ.range ht ht' hC1
  have hmkσ' : ∀ c, QuotientAddGroup.mk' φ.range (σC c) = σR (QuotientAddGroup.mk' φ.range c) :=
    mk'_quotAut σC φ.range ht ht'

  let T₂ : HerbrandTriple (I ⧸ κ.range) C (C ⧸ φ.range) :=
    { P := ofAddAut σQ n hQ1
      Q := ofAddAut σC n hC1
      R := ofAddAut σR n hRn
      ι := φ'
      π := QuotientAddGroup.mk' φ.range
      ι_injective := hφ'inj
      π_surjective := QuotientAddGroup.mk'_surjective _
      exact := by rw [hφ'range]; exact (QuotientAddGroup.ker_mk' φ.range).symm
      derive_ι := derive_comm σQ σC φ' hφ'σ hQ1 hC1
      norm_ι := norm_comm σQ σC φ' hφ'σ hQ1 hC1
      derive_π := derive_comm σC σR _ hmkσ' hC1 hRn
      norm_π := norm_comm σC σR _ hmkσ' hC1 hRn }
  haveI := hfin
  have h2 : T₁.R.tateCard₀ * (ofAddAut σC n hC1).tateCard₁ =
      (ofAddAut σC n hC1).tateCard₀ * T₁.R.tateCard₁ := T₂.tateCard_mul_of_finite_quot
  rw [h1] at h2
  have h3 : (ofAddAut σC n hC1).tateCard₀ * T₁.R.tateCard₁ =
      n * (ofAddAut σC n hC1).tateCard₁ * T₁.R.tateCard₁ := by
    rw [← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hR1) h3

theorem dvd_tateCard₀_of_shape (σU : AddAut U) (σI : AddAut I) (σC : AddAut C) {n : ℕ}
    (hU1 : σU ^ n = 1) (hI1 : σI ^ n = 1) (hC1 : σC ^ n = 1)
    (κ : U →+ I) (φ : I →+ C)
    (hκ : Function.Injective κ) (hκσ : ∀ u, κ (σU u) = σI (κ u)) (hφσ : ∀ i, φ (σI i) = σC (φ i))
    (hex : κ.range = φ.ker) (hfin : Finite (C ⧸ φ.range)) {N : ℕ}
    (hI : (ofAddAut σI n hI1).tateCard₀ = N * (ofAddAut σI n hI1).tateCard₁)
    (hU : (ofAddAut σU n hU1).tateCard₀ * n = N * (ofAddAut σU n hU1).tateCard₁)
    (hpos : (ofAddAut σU n hU1).tateCard₀ * (ofAddAut σI n hI1).tateCard₁ ≠ 0) :
    n ∣ (ofAddAut σC n hC1).tateCard₀ :=
  ⟨_, tateCard₀_eq_of_shape σU σI σC hU1 hI1 hC1 κ φ hκ hκσ hφσ hex hfin hI hU hpos⟩

end Shape
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

section Control

example {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite B] (σ : AddAut A) (τ : AddAut B) {n N : ℕ}
    (hσ : σ ^ n = 1) (hτ : τ ^ n = 1)
    (hI : (ofAddAut σ n hσ).tateCard₀ = N * (ofAddAut σ n hσ).tateCard₁)
    (hU : (ofAddAut σ n hσ).tateCard₀ * n = N * (ofAddAut σ n hσ).tateCard₁)
    (hpos : (ofAddAut σ n hσ).tateCard₀ * (ofAddAut σ n hσ).tateCard₁ ≠ 0) :
    (ofAddAut τ n hτ).tateCard₀ = n * (ofAddAut τ n hτ).tateCard₁ :=
  tateCard₀_eq_of_shape σ σ τ hσ hσ hτ (AddMonoidHom.id A) 0 Function.injective_id (fun _ => rfl)
    (fun _ => (map_zero τ).symm)
    (by rw [AddMonoidHom.range_eq_top_of_surjective _ Function.surjective_id, AddMonoidHom.ker_zero])
    (Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _)) hI hU hpos

end Control
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

end M4aHerbrand.FirstInequalityShape
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

end
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

end Fold_FirstInequalityShape
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

section Fold_SemilocalHerbrand

open Finset

namespace M4aLocalCFT

open HerbrandPair LocalUnitsCohomology

namespace SemilocalHerbrand

variable (d m : ℕ) {M : Type*} [AddCommGroup M] (τ : AddAut M)

def twistedShiftAut : AddAut (ZMod d → M) where
  toFun f := fun i => if i + 1 = 0 then τ (f (i + 1)) else f (i + 1)
  invFun f := fun i => if i = 0 then τ.symm (f (i - 1)) else f (i - 1)
  left_inv f := by
    funext i
    have h1 : i - 1 + 1 = i := by ring
    simp only [h1]
    split_ifs with h
    · exact τ.symm_apply_apply _
    · rfl
  right_inv f := by
    funext i
    have h1 : i + 1 - 1 = i := by ring
    simp only [h1]
    split_ifs with h
    · exact τ.apply_symm_apply _
    · rfl
  map_add' f g := by
    funext i
    by_cases h : (i : ZMod d) + 1 = 0
    · simp only [Pi.add_apply, if_pos h, map_add]
    · simp only [Pi.add_apply, if_neg h]

@[scoped simp] theorem twistedShiftAut_apply (f : ZMod d → M) (i : ZMod d) :
    twistedShiftAut d τ f i = if i + 1 = 0 then τ (f (i + 1)) else f (i + 1) := rfl

private theorem _root_.M4aLocalCFT.SemilocalHerbrand.cast_succ (a : ℕ) :
    (((a + 1 : ℕ)) : ZMod d) = ((a : ℕ) : ZMod d) + 1 := by
  rw [Nat.cast_add, Nat.cast_one]

p2m_export "M4aLocalCFT.SemilocalHerbrand" "cast_succ"
variable [NeZero d]

private theorem d_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)

omit [NeZero d] in

private theorem natCast_eq_zero_iff (j : ℕ) (hj0 : 0 < j) (hj : j < 2 * d) :
    ((j : ℕ) : ZMod d) = 0 ↔ j = d := by
  constructor
  · intro h
    rcases lt_trichotomy j d with hlt | heq | hgt
    · exfalso
      have hv := ZMod.val_cast_of_lt hlt
      rw [h, ZMod.val_zero] at hv
      omega
    · exact heq
    · exfalso
      have hcast : ((j - d : ℕ) : ZMod d) = 0 := by
        have hj' : ((j : ℕ) : ZMod d) = ((j - d : ℕ) : ZMod d) := by
          conv_lhs => rw [show j = (j - d) + d by omega]
          rw [Nat.cast_add, ZMod.natCast_self, add_zero]
        rw [← hj']
        exact h
      have hv := ZMod.val_cast_of_lt (show j - d < d by omega)
      rw [hcast, ZMod.val_zero] at hv
      omega
  · intro h
    rw [h]
    exact ZMod.natCast_self d

omit [NeZero d] in

theorem twistedShiftAut_pow_apply_le (a : ℕ) (ha : a < d) :
    ∀ (k : ℕ), k ≤ d → ∀ (f : ZMod d → M),
      ((twistedShiftAut d τ) ^ k) f ((a : ℕ) : ZMod d)
        = if a + k < d then f (((a + k : ℕ)) : ZMod d)
          else τ (f (((a + k : ℕ)) : ZMod d)) := by
  intro k
  induction k with
  | zero =>
      intro _ f
      rw [pow_zero, AddAut.one_apply', if_pos (by omega), Nat.add_zero]
  | succ k ih =>
      intro hk f
      rw [pow_succ, AddAut.mul_apply', ih (by omega) (twistedShiftAut d τ f)]
      have hiff : (((a + k + 1 : ℕ)) : ZMod d) = 0 ↔ a + k + 1 = d :=
        natCast_eq_zero_iff d (a + k + 1) (by omega) (by omega)
      simp only [twistedShiftAut_apply, ← cast_succ, hiff]
      split_ifs <;> first | rfl | (exfalso; omega)

theorem twistedShiftAut_pow_d_apply (f : ZMod d → M) (i : ZMod d) :
    ((twistedShiftAut d τ) ^ d) f i = τ (f i) := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, a < d ∧ ((a : ℕ) : ZMod d) = i :=
    ⟨i.val, ZMod.val_lt i, ZMod.natCast_rightInverse i⟩
  rw [twistedShiftAut_pow_apply_le d τ a ha d le_rfl f, if_neg (by omega),
    show (((a + d : ℕ)) : ZMod d) = ((a : ℕ) : ZMod d) by
      rw [Nat.cast_add, ZMod.natCast_self, add_zero]]

theorem twistedShiftAut_pow_apply_zero (r : ℕ) (hr : r < d) (f : ZMod d → M) :
    ((twistedShiftAut d τ) ^ r) f 0 = f ((r : ℕ) : ZMod d) := by
  have h0 : (((0 : ℕ)) : ZMod d) = (0 : ZMod d) := Nat.cast_zero
  rw [← h0, twistedShiftAut_pow_apply_le d τ 0 (d_pos d) r (by omega) f,
    if_pos (by omega), Nat.zero_add]

theorem twistedShiftAut_pow_d_mul_apply (q : ℕ) (f : ZMod d → M) (i : ZMod d) :
    ((twistedShiftAut d τ) ^ (d * q)) f i = (τ ^ q) (f i) := by
  induction q generalizing f with
  | zero =>
      rw [Nat.mul_zero, pow_zero, pow_zero, AddAut.one_apply', AddAut.one_apply']
  | succ q ih =>
      rw [Nat.mul_succ, pow_add, AddAut.mul_apply', ih, twistedShiftAut_pow_d_apply,
        pow_succ, AddAut.mul_apply']

theorem twistedShiftAut_pow_card (hτ : τ ^ m = 1) :
    (twistedShiftAut d τ) ^ (d * m) = 1 := by
  refine AddEquiv.ext fun f => funext fun i => ?_
  rw [twistedShiftAut_pow_d_mul_apply, hτ, AddAut.one_apply', AddAut.one_apply']

noncomputable def coinducedPair (hτ : τ ^ m = 1) : HerbrandPair (ZMod d → M) :=
  HerbrandPair.ofAddAut (twistedShiftAut d τ) (d * m) (twistedShiftAut_pow_card d m τ hτ)

theorem coinducedPair_derive_apply (hτ : τ ^ m = 1) (f : ZMod d → M) :
    (coinducedPair d m τ hτ).derive f = twistedShiftAut d τ f - f :=
  HerbrandPair.ofAddAut_derive_apply _ _ _ f

theorem apply_eq_apply_zero_of_derive_eq_zero (hτ : τ ^ m = 1) {f : ZMod d → M}
    (hf : (coinducedPair d m τ hτ).derive f = 0) (i : ZMod d) : f i = f 0 := by
  have hstep : ∀ j : ZMod d, j + 1 ≠ 0 → f (j + 1) = f j := by
    intro j hj
    have h := congrFun hf j
    rw [coinducedPair_derive_apply, Pi.sub_apply, Pi.zero_apply, sub_eq_zero,
      twistedShiftAut_apply, if_neg hj] at h
    exact h
  have key : ∀ a : ℕ, a < d → f ((a : ℕ) : ZMod d) = f 0 := by
    intro a
    induction a with
    | zero => intro _; rw [Nat.cast_zero]
    | succ a ih =>
        intro ha
        have hne : ((a : ℕ) : ZMod d) + 1 ≠ 0 := by
          rw [← cast_succ]
          intro h0
          have := (natCast_eq_zero_iff d (a + 1) (by omega) (by omega)).mp h0
          omega
        rw [cast_succ, hstep _ hne]
        exact ih (by omega)
  obtain ⟨a, ha, rfl⟩ : ∃ a, a < d ∧ ((a : ℕ) : ZMod d) = i :=
    ⟨i.val, ZMod.val_lt i, ZMod.natCast_rightInverse i⟩
  exact key a ha

theorem apply_zero_fixed_of_derive_eq_zero (hτ : τ ^ m = 1) {f : ZMod d → M}
    (hf : (coinducedPair d m τ hτ).derive f = 0) : τ (f 0) = f 0 := by
  have h := congrFun hf (-1)
  rw [coinducedPair_derive_apply, Pi.sub_apply, Pi.zero_apply, sub_eq_zero,
    twistedShiftAut_apply, if_pos (by ring : (-1 : ZMod d) + 1 = 0),
    (by ring : (-1 : ZMod d) + 1 = 0)] at h
  rw [h]
  exact apply_eq_apply_zero_of_derive_eq_zero d m τ hτ hf (-1)

theorem derive_const_eq_zero (hτ : τ ^ m = 1) {c : M} (hc : τ c = c) :
    (coinducedPair d m τ hτ).derive (fun _ => c) = 0 := by
  rw [coinducedPair_derive_apply]
  funext i
  rw [Pi.sub_apply, Pi.zero_apply, twistedShiftAut_apply]
  split_ifs <;> simp [hc]

omit [NeZero d] in

def coinducedTrace : (ZMod d → M) →+ M where
  toFun f := ∑ r ∈ range d, f ((r : ℕ) : ZMod d)
  map_zero' := by simp
  map_add' f g := by
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib

omit [NeZero d] in
@[scoped simp] theorem coinducedTrace_apply (f : ZMod d → M) :
    coinducedTrace d f = ∑ r ∈ range d, f ((r : ℕ) : ZMod d) := rfl

private def delta (c : M) : ZMod d → M := fun j => if j = 0 then c else 0

private theorem coinducedTrace_delta (c : M) : coinducedTrace d (delta d c) = c := by
  rw [coinducedTrace_apply]
  have key : (∑ r ∈ Finset.range d, delta d c ((r : ℕ) : ZMod d))
      = delta d c (((0 : ℕ)) : ZMod d) := by
    refine Finset.sum_eq_single 0 (fun r hr hr0 => ?_) (fun h => ?_)
    · refine if_neg fun hcast => hr0 ?_
      have hv := ZMod.val_cast_of_lt (Finset.mem_range.mp hr)
      rw [hcast, ZMod.val_zero] at hv
      exact hv.symm
    · exact absurd (Finset.mem_range.mpr (d_pos d)) h
  rw [key]
  show (if (((0 : ℕ)) : ZMod d) = 0 then c else 0) = c
  rw [if_pos Nat.cast_zero]

private theorem sum_pow_apply_zero (q : ℕ) (f : ZMod d → M) :
    ∑ j ∈ range (d * q), ((twistedShiftAut d τ) ^ j) f 0
      = ∑ p ∈ range q, (τ ^ p) (coinducedTrace d f) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      rw [coinducedTrace_apply, map_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [pow_add, AddAut.mul_apply', twistedShiftAut_pow_d_mul_apply,
        twistedShiftAut_pow_apply_zero d τ r (Finset.mem_range.mp hr)]

theorem coinducedPair_norm_apply_zero (hτ : τ ^ m = 1) (f : ZMod d → M) :
    (coinducedPair d m τ hτ).norm f 0
      = (HerbrandPair.ofAddAut τ m hτ).norm (coinducedTrace d f) := by
  rw [show (coinducedPair d m τ hτ).norm f
      = ∑ j ∈ range (d * m), ((twistedShiftAut d τ) ^ j) f from
    HerbrandPair.ofAddAut_norm_apply _ _ _ f]
  rw [HerbrandPair.ofAddAut_norm_apply, Finset.sum_apply]
  exact sum_pow_apply_zero d τ m f

theorem coinducedPair_norm_apply (hτ : τ ^ m = 1) (f : ZMod d → M) (i : ZMod d) :
    (coinducedPair d m τ hτ).norm f i
      = (HerbrandPair.ofAddAut τ m hτ).norm (coinducedTrace d f) := by
  rw [← coinducedPair_norm_apply_zero d m τ hτ f]
  exact apply_eq_apply_zero_of_derive_eq_zero d m τ hτ
    ((coinducedPair d m τ hτ).derive_norm f) i

section DegreeZero

variable (hτ : τ ^ m = 1)

private theorem evalZero_mem (f : (coinducedPair d m τ hτ).derive.ker) :
    (f : ZMod d → M) 0 ∈ (HerbrandPair.ofAddAut τ m hτ).derive.ker := by
  rw [AddMonoidHom.mem_ker, HerbrandPair.ofAddAut_derive_apply, sub_eq_zero]
  exact apply_zero_fixed_of_derive_eq_zero d m τ hτ (AddMonoidHom.mem_ker.mp f.2)

private noncomputable def tateZeroCompare :
    (coinducedPair d m τ hτ).derive.ker →+
      ((HerbrandPair.ofAddAut τ m hτ).derive.ker ⧸
        (HerbrandPair.ofAddAut τ m hτ).norm.range.addSubgroupOf
          (HerbrandPair.ofAddAut τ m hτ).derive.ker) where
  toFun f := QuotientAddGroup.mk ⟨(f : ZMod d → M) 0, evalZero_mem d m τ hτ f⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem tateZeroCompare_surjective :
    Function.Surjective (tateZeroCompare d m τ hτ) := by
  intro y
  refine QuotientAddGroup.induction_on y fun c => ?_
  have hc : τ (c : M) = (c : M) := by
    have h := AddMonoidHom.mem_ker.mp c.2
    rw [HerbrandPair.ofAddAut_derive_apply, sub_eq_zero] at h
    exact h
  exact ⟨⟨fun _ => (c : M), AddMonoidHom.mem_ker.mpr
    (derive_const_eq_zero d m τ hτ hc)⟩,
    congrArg QuotientAddGroup.mk (Subtype.ext rfl)⟩

private theorem tateZeroCompare_ker :
    (tateZeroCompare d m τ hτ).ker
      = (coinducedPair d m τ hτ).norm.range.addSubgroupOf
          (coinducedPair d m τ hτ).derive.ker := by
  ext f
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, tateZeroCompare,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨delta d x, ?_⟩
    funext i
    rw [coinducedPair_norm_apply d m τ hτ _ i, coinducedTrace_delta, hx]
    exact (apply_eq_apply_zero_of_derive_eq_zero d m τ hτ
      (AddMonoidHom.mem_ker.mp f.2) i).symm
  · rintro ⟨g, hg⟩
    exact ⟨coinducedTrace d g, by
      rw [← coinducedPair_norm_apply_zero d m τ hτ g, hg]⟩

theorem tateCard₀_coinducedPair :
    (coinducedPair d m τ hτ).tateCard₀ = (HerbrandPair.ofAddAut τ m hτ).tateCard₀ := by
  rw [HerbrandPair.tateCard₀, HerbrandPair.tateCard₀, ← tateZeroCompare_ker d m τ hτ]
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (tateZeroCompare_surjective d m τ hτ)).toEquiv

end DegreeZero
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

theorem coinducedTrace_twistedShiftAut (g : ZMod d → M) :
    coinducedTrace d (twistedShiftAut d τ g)
      = coinducedTrace d g + (τ (g 0) - g 0) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by have := d_pos d; omega⟩
  simp only [coinducedTrace_apply]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hwrap : (((e : ℕ)) : ZMod (e + 1)) + 1 = 0 := by
    rw [← cast_succ, ZMod.natCast_self]
  have hterm : ∀ r ∈ range e,
      twistedShiftAut (e + 1) τ g ((r : ℕ) : ZMod (e + 1))
        = g (((r + 1 : ℕ)) : ZMod (e + 1)) := by
    intro r hr
    rw [twistedShiftAut_apply, ← cast_succ, if_neg]
    intro h0
    have := (natCast_eq_zero_iff (e + 1) (r + 1) (by omega)
      (by have := Finset.mem_range.mp hr; omega)).mp h0
    have := Finset.mem_range.mp hr
    omega
  rw [Finset.sum_congr rfl hterm, twistedShiftAut_apply, if_pos hwrap, hwrap,
    Nat.cast_zero]
  abel

private theorem coinducedPair_derive_partialSum (hτ : τ ^ m = 1) (f : ZMod d → M)
    (x : M) (hx : τ x - x = coinducedTrace d f) :
    (coinducedPair d m τ hτ).derive
      (fun j => x + ∑ k ∈ range j.val, f ((k : ℕ) : ZMod d)) = f := by
  rw [coinducedPair_derive_apply]
  funext i
  obtain ⟨a, ha, rfl⟩ : ∃ a, a < d ∧ ((a : ℕ) : ZMod d) = i :=
    ⟨i.val, ZMod.val_lt i, ZMod.natCast_rightInverse i⟩
  rw [Pi.sub_apply, twistedShiftAut_apply, ← cast_succ]
  by_cases hwrap : a + 1 = d
  ·
    have h0 : (((a + 1 : ℕ)) : ZMod d) = 0 := by rw [hwrap]; exact ZMod.natCast_self d
    rw [if_pos h0, h0]
    show τ (x + ∑ k ∈ range (0 : ZMod d).val, f ((k : ℕ) : ZMod d))
        - (x + ∑ k ∈ range ((a : ℕ) : ZMod d).val, f ((k : ℕ) : ZMod d))
        = f ((a : ℕ) : ZMod d)
    rw [ZMod.val_zero, Finset.sum_range_zero, add_zero, ZMod.val_cast_of_lt ha]
    have hsum : (∑ r ∈ range d, f ((r : ℕ) : ZMod d))
        = (∑ k ∈ range a, f ((k : ℕ) : ZMod d)) + f ((a : ℕ) : ZMod d) := by
      rw [show range d = range (a + 1) by rw [hwrap], Finset.sum_range_succ]
    have htx : τ x - x
        = (∑ k ∈ range a, f ((k : ℕ) : ZMod d)) + f ((a : ℕ) : ZMod d) := by
      rw [hx, coinducedTrace_apply, hsum]
    calc τ x - (x + ∑ k ∈ range a, f ((k : ℕ) : ZMod d))
        = (τ x - x) - ∑ k ∈ range a, f ((k : ℕ) : ZMod d) := by abel
      _ = ((∑ k ∈ range a, f ((k : ℕ) : ZMod d)) + f ((a : ℕ) : ZMod d))
            - ∑ k ∈ range a, f ((k : ℕ) : ZMod d) := by rw [htx]
      _ = f ((a : ℕ) : ZMod d) := by abel
  ·
    have hlt : a + 1 < d := by omega
    have hne : (((a + 1 : ℕ)) : ZMod d) ≠ 0 := by
      intro h0
      have := (natCast_eq_zero_iff d (a + 1) (by omega) (by omega)).mp h0
      omega
    rw [if_neg hne]
    show (x + ∑ k ∈ range (((a + 1 : ℕ)) : ZMod d).val, f ((k : ℕ) : ZMod d))
        - (x + ∑ k ∈ range ((a : ℕ) : ZMod d).val, f ((k : ℕ) : ZMod d))
        = f ((a : ℕ) : ZMod d)
    rw [ZMod.val_cast_of_lt hlt, ZMod.val_cast_of_lt ha, Finset.sum_range_succ]
    abel

section DegreeOne

variable (hτ : τ ^ m = 1)

private theorem traceKer_mem (f : (coinducedPair d m τ hτ).norm.ker) :
    coinducedTrace d (f : ZMod d → M) ∈ (HerbrandPair.ofAddAut τ m hτ).norm.ker := by
  rw [AddMonoidHom.mem_ker]
  have h0 := congrFun (AddMonoidHom.mem_ker.mp f.2) 0
  rw [coinducedPair_norm_apply_zero d m τ hτ, Pi.zero_apply] at h0
  exact h0

private noncomputable def tateOneCompare :
    (coinducedPair d m τ hτ).norm.ker →+
      ((HerbrandPair.ofAddAut τ m hτ).norm.ker ⧸
        (HerbrandPair.ofAddAut τ m hτ).derive.range.addSubgroupOf
          (HerbrandPair.ofAddAut τ m hτ).norm.ker) where
  toFun f := QuotientAddGroup.mk ⟨coinducedTrace d (f : ZMod d → M),
    traceKer_mem d m τ hτ f⟩
  map_zero' := by
    refine congrArg QuotientAddGroup.mk (Subtype.ext ?_)
    exact map_zero (coinducedTrace d)
  map_add' f g := by
    refine congrArg QuotientAddGroup.mk (Subtype.ext ?_)
    exact map_add (coinducedTrace d) _ _

private theorem tateOneCompare_surjective :
    Function.Surjective (tateOneCompare d m τ hτ) := by
  intro y
  refine QuotientAddGroup.induction_on y fun c => ?_
  have hc : (HerbrandPair.ofAddAut τ m hτ).norm (c : M) = 0 := AddMonoidHom.mem_ker.mp c.2
  refine ⟨⟨delta d (c : M), AddMonoidHom.mem_ker.mpr ?_⟩, ?_⟩
  · funext i
    rw [coinducedPair_norm_apply d m τ hτ _ i, coinducedTrace_delta, hc, Pi.zero_apply]
  · exact congrArg QuotientAddGroup.mk (Subtype.ext (coinducedTrace_delta d (c : M)))

private theorem tateOneCompare_ker :
    (tateOneCompare d m τ hτ).ker
      = (coinducedPair d m τ hτ).derive.range.addSubgroupOf
          (coinducedPair d m τ hτ).norm.ker := by
  ext f
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, tateOneCompare,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨x, hx⟩
    rw [HerbrandPair.ofAddAut_derive_apply] at hx
    exact ⟨fun j => x + ∑ k ∈ range j.val, (f : ZMod d → M) ((k : ℕ) : ZMod d),
      coinducedPair_derive_partialSum d m τ hτ (f : ZMod d → M) x hx⟩
  · rintro ⟨g, hg⟩
    refine ⟨g 0, ?_⟩
    rw [HerbrandPair.ofAddAut_derive_apply]
    show τ (g 0) - g 0 = coinducedTrace d (f : ZMod d → M)
    have htr := congrArg (coinducedTrace d) hg
    rw [coinducedPair_derive_apply, map_sub, coinducedTrace_twistedShiftAut] at htr
    rw [← htr]
    abel

theorem tateCard₁_coinducedPair :
    (coinducedPair d m τ hτ).tateCard₁ = (HerbrandPair.ofAddAut τ m hτ).tateCard₁ := by
  rw [HerbrandPair.tateCard₁, HerbrandPair.tateCard₁, ← tateOneCompare_ker d m τ hτ]
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (tateOneCompare_surjective d m τ hτ)).toEquiv

end DegreeOne
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

theorem herbrandQuotient_coinducedPair (hτ : τ ^ m = 1) :
    (coinducedPair d m τ hτ).tateCard₀ = (HerbrandPair.ofAddAut τ m hτ).tateCard₀
      ∧ (coinducedPair d m τ hτ).tateCard₁ = (HerbrandPair.ofAddAut τ m hτ).tateCard₁ :=
  ⟨tateCard₀_coinducedPair d m τ hτ, tateCard₁_coinducedPair d m τ hτ⟩

theorem isCohTrivial_coinducedPair_iff (hτ : τ ^ m = 1) :
    IsCohTrivial (coinducedPair d m τ hτ)
      ↔ IsCohTrivial (HerbrandPair.ofAddAut τ m hτ) := by
  unfold IsCohTrivial
  rw [tateCard₀_coinducedPair d m τ hτ, tateCard₁_coinducedPair d m τ hτ]

section Gates

private theorem negAddAut_apply (a : ℤ) : negAddAut ℤ a = -a := rfl

theorem tateCard₀_coinducedPair_int (hm : m ≠ 0) :
    (coinducedPair d m (1 : AddAut ℤ) (one_pow m)).tateCard₀ = m := by
  rw [tateCard₀_coinducedPair d m (1 : AddAut ℤ) (one_pow m)]
  exact tateCard₀_intCyclicPair hm

theorem coinducedPair_not_isCohTrivial :
    ¬ IsCohTrivial (coinducedPair 2 2 (1 : AddAut ℤ) (one_pow 2)) := by
  intro h
  have h2 := tateCard₀_coinducedPair_int 2 2 (by omega)
  rw [h.1] at h2
  omega

theorem twistedShiftAut_const_ne :
    twistedShiftAut 2 (negAddAut ℤ) (fun _ => (1 : ℤ)) ≠ (fun _ => (1 : ℤ)) := by
  intro h
  have happ := congrFun h 1
  rw [twistedShiftAut_apply, if_pos (by decide : (1 : ZMod 2) + 1 = 0)] at happ
  exact absurd (show (-1 : ℤ) = 1 from happ) (by omega)

theorem tateCard₁_negPair :
    (HerbrandPair.ofAddAut (negAddAut ℤ) 2 (negAddAut_sq ℤ)).tateCard₁ = 2 := by
  have hnorm : ∀ a : ℤ,
      (HerbrandPair.ofAddAut (negAddAut ℤ) 2 (negAddAut_sq ℤ)).norm a = 0 := by
    intro a
    rw [HerbrandPair.ofAddAut_norm_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
      pow_one, AddAut.one_apply', negAddAut_apply]
    ring
  have hderive : ∀ a : ℤ,
      (HerbrandPair.ofAddAut (negAddAut ℤ) 2 (negAddAut_sq ℤ)).derive a = -(2 * a) := by
    intro a
    rw [HerbrandPair.ofAddAut_derive_apply, negAddAut_apply]
    ring
  have hsurj : Function.Surjective ((Int.castAddHom (ZMod 2)).comp
      (HerbrandPair.ofAddAut (negAddAut ℤ) 2 (negAddAut_sq ℤ)).norm.ker.subtype) := by
    intro z
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective z
    exact ⟨⟨a, AddMonoidHom.mem_ker.mpr (hnorm a)⟩, ha⟩
  have hker : ((Int.castAddHom (ZMod 2)).comp
      (HerbrandPair.ofAddAut (negAddAut ℤ) 2 (negAddAut_sq ℤ)).norm.ker.subtype).ker
      = (HerbrandPair.ofAddAut (negAddAut ℤ) 2
          (negAddAut_sq ℤ)).derive.range.addSubgroupOf
        (HerbrandPair.ofAddAut (negAddAut ℤ) 2 (negAddAut_sq ℤ)).norm.ker := by
    ext ⟨x, hx⟩
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
      AddSubgroup.coe_subtype, Int.coe_castAddHom, AddSubgroup.mem_addSubgroupOf,
      AddMonoidHom.mem_range]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨-a, by rw [hderive]; omega⟩
    · rintro ⟨a, ha⟩
      rw [hderive] at ha
      exact ⟨-a, by omega⟩
  rw [HerbrandPair.tateCard₁, ← hker]
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]
  exact Nat.card_zmod 2

theorem tateCard₁_coinducedPair_neg :
    (coinducedPair 3 2 (negAddAut ℤ) (negAddAut_sq ℤ)).tateCard₁ = 2 := by
  rw [tateCard₁_coinducedPair 3 2 (negAddAut ℤ) (negAddAut_sq ℤ)]
  exact tateCard₁_negPair

theorem isCohTrivial_ofAddAut_one (σ : AddAut M) (hσ : σ ^ 1 = 1) :
    IsCohTrivial (HerbrandPair.ofAddAut σ 1 hσ) := by
  have hσ1 : σ = 1 := by rw [← pow_one σ, hσ]
  have hnorm : ∀ a : M, (HerbrandPair.ofAddAut σ 1 hσ).norm a = a := by
    intro a
    rw [HerbrandPair.ofAddAut_norm_apply, Finset.sum_range_one, pow_zero,
      AddAut.one_apply']
  constructor
  ·
    rw [HerbrandPair.tateCard₀, Nat.card_eq_one_iff_exists]
    refine ⟨QuotientAddGroup.mk 0, fun y => QuotientAddGroup.induction_on y fun x => ?_⟩
    refine (QuotientAddGroup.eq.mpr ?_).symm
    rw [AddSubgroup.mem_addSubgroupOf]
    exact ⟨((-(0 : (HerbrandPair.ofAddAut σ 1 hσ).derive.ker) + x :
      (HerbrandPair.ofAddAut σ 1 hσ).derive.ker) : M), hnorm _⟩
  ·
    rw [HerbrandPair.tateCard₁, Nat.card_eq_one_iff_exists]
    have hker : ∀ x : (HerbrandPair.ofAddAut σ 1 hσ).norm.ker, x = 0 := by
      rintro ⟨x, hx⟩
      rw [AddMonoidHom.mem_ker, hnorm] at hx
      exact Subtype.ext hx
    exact ⟨QuotientAddGroup.mk 0, fun y =>
      QuotientAddGroup.induction_on y fun x => congrArg QuotientAddGroup.mk (hker x)⟩

theorem isCohTrivial_coinducedPair_one :
    IsCohTrivial (coinducedPair d 1 (1 : AddAut M) (one_pow 1)) :=
  (isCohTrivial_coinducedPair_iff d 1 (1 : AddAut M) (one_pow 1)).mpr
    (isCohTrivial_ofAddAut_one (1 : AddAut M) (one_pow 1))

end Gates
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite"

end SemilocalHerbrand
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

end Fold_SemilocalHerbrand
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

section Fold_IdempotentCycleShapiro

set_option autoImplicit false

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace IdempotentCycle
p2m_open "M4aHerbrand"

open M4aLocalCFT M4aLocalCFT.HerbrandPair M4aLocalCFT.SemilocalHerbrand M4aLocalCFT.LocalUnitsCohomology

section Transport

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem tateCard₀_congr (P : HerbrandPair A) (Q : HerbrandPair B) (Φ : A ≃+ B)
    (hd : ∀ a, Q.derive (Φ a) = Φ (P.derive a)) (hn : ∀ a, Q.norm (Φ a) = Φ (P.norm a)) :
    P.tateCard₀ = Q.tateCard₀ := by
  unfold HerbrandPair.tateCard₀

  have hker : ∀ a, a ∈ P.derive.ker ↔ Φ a ∈ Q.derive.ker := fun a => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hd, Φ.map_eq_zero_iff]
  let Φk : P.derive.ker ≃+ Q.derive.ker :=
    { toFun := fun a => ⟨Φ a.1, (hker a.1).mp a.2⟩
      invFun := fun b => ⟨Φ.symm b.1, (hker _).mpr (by rw [Φ.apply_symm_apply]; exact b.2)⟩
      left_inv := fun a => Subtype.ext (Φ.symm_apply_apply a.1)
      right_inv := fun b => Subtype.ext (Φ.apply_symm_apply b.1)
      map_add' := fun a b => Subtype.ext (map_add Φ a.1 b.1) }
  have hΦk : ∀ a : P.derive.ker, (Φk a).1 = Φ a.1 := fun a => rfl
  have hmap : (P.norm.range.addSubgroupOf P.derive.ker).map Φk.toAddMonoidHom =
      Q.norm.range.addSubgroupOf Q.derive.ker := by
    ext b
    rw [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at ha
      obtain ⟨a', ha'⟩ := ha
      refine ⟨Φ a', ?_⟩
      rw [AddEquiv.coe_toAddMonoidHom, hΦk, hn, ha']
    · rintro ⟨b', hb'⟩
      refine ⟨Φk.symm b, ?_, Φk.apply_symm_apply b⟩
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
      refine ⟨Φ.symm b', ?_⟩
      apply Φ.injective
      rw [← hn, Φ.apply_symm_apply, hb']
      show b.1 = Φ (Φk.symm b).1
      rw [← hΦk, Φk.apply_symm_apply]
  rw [← hmap]
  exact Nat.card_congr (QuotientAddGroup.congr _ _ Φk rfl).toEquiv

theorem tateCard₁_congr (P : HerbrandPair A) (Q : HerbrandPair B) (Φ : A ≃+ B)
    (hd : ∀ a, Q.derive (Φ a) = Φ (P.derive a)) (hn : ∀ a, Q.norm (Φ a) = Φ (P.norm a)) :
    P.tateCard₁ = Q.tateCard₁ := by

  have := tateCard₀_congr P.swap Q.swap Φ hn hd
  simp [HerbrandPair.tateCard₀, HerbrandPair.tateCard₁, HerbrandPair.swap] at this
  exact this

theorem semiconj_pow (α : AddAut A) (β : AddAut B) (Φ : A ≃+ B) (h : ∀ a, Φ (α a) = β (Φ a)) (k : ℕ) (a : A) :
    Φ ((α ^ k) a) = (β ^ k) (Φ a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AddAut.mul_apply', AddAut.mul_apply', ih, h]

theorem tateCard₀_ofAddAut_congr (α : AddAut A) (β : AddAut B) (Φ : A ≃+ B) (h : ∀ a, Φ (α a) = β (Φ a))
    (n : ℕ) (hα : α ^ n = 1) (hβ : β ^ n = 1) :
    (ofAddAut α n hα).tateCard₀ = (ofAddAut β n hβ).tateCard₀ := by
  refine tateCard₀_congr _ _ Φ (fun a => ?_) (fun a => ?_)
  · rw [ofAddAut_derive_apply, ofAddAut_derive_apply, map_sub, h]
  · rw [ofAddAut_norm_apply, ofAddAut_norm_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => (semiconj_pow α β Φ h k a).symm

theorem tateCard₁_ofAddAut_congr (α : AddAut A) (β : AddAut B) (Φ : A ≃+ B) (h : ∀ a, Φ (α a) = β (Φ a))
    (n : ℕ) (hα : α ^ n = 1) (hβ : β ^ n = 1) :
    (ofAddAut α n hα).tateCard₁ = (ofAddAut β n hβ).tateCard₁ := by
  refine tateCard₁_congr _ _ Φ (fun a => ?_) (fun a => ?_)
  · rw [ofAddAut_derive_apply, ofAddAut_derive_apply, map_sub, h]
  · rw [ofAddAut_norm_apply, ofAddAut_norm_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => (semiconj_pow α β Φ h k a).symm

end Transport
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

section Cycle

variable {C : Type*} [CommRing C] {d : ℕ} [NeZero d]
variable (σ : C ≃+* C) (e : ZMod d → C) (hσe : ∀ i, σ (e i) = e (i + 1))

omit [NeZero d] in
include hσe in
theorem pow_apply_e (k : ℕ) (i : ZMod d) : (σ ^ k) (e i) = e (i + k) := by
  induction k generalizing i with
  | zero => rw [pow_zero, RingAut.one_apply, Nat.cast_zero, add_zero]
  | succ k ih => rw [pow_succ, RingAut.mul_apply, hσe, ih, Nat.cast_succ, add_assoc, add_comm 1]

omit [NeZero d] in
include hσe in
theorem symm_pow_apply_e (k : ℕ) (i : ZMod d) : (σ ^ k).symm (e i) = e (i - k) := by
  apply (σ ^ k).injective
  rw [RingEquiv.apply_symm_apply, pow_apply_e σ e hσe, sub_add_cancel]

omit [NeZero d] in
include hσe in
theorem pow_d_apply_e (i : ZMod d) : (σ ^ d) (e i) = e i := by
  rw [pow_apply_e σ e hσe, ZMod.natCast_self, add_zero]

end Cycle
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

section Corner

variable {C : Type*} [CommRing C] {d : ℕ} [NeZero d]
variable (e : ZMod d → C) (he : CompleteOrthogonalIdempotents e)

private abbrev _root_.M4aHerbrand.IdempotentCycle.Corner : Type _ := (he.idem 0).Corner

p2m_export "M4aHerbrand.IdempotentCycle" "Corner"

def cornerProj : C →+* Corner e he where
  toFun x := ⟨e 0 * x * e 0, x, rfl⟩
  map_one' := Subtype.ext (by show e 0 * 1 * e 0 = e 0; rw [mul_one, (he.idem 0).eq])
  map_mul' x y := Subtype.ext (by
    show e 0 * (x * y) * e 0 = (e 0 * x * e 0) * (e 0 * y * e 0)
    have h := (he.idem 0).eq
    calc e 0 * (x * y) * e 0 = (e 0 * e 0) * x * ((e 0 * e 0) * y) := by rw [h]; ring
      _ = (e 0 * x * e 0) * (e 0 * y * e 0) := by ring)
  map_zero' := Subtype.ext (by show e 0 * 0 * e 0 = 0; rw [mul_zero, zero_mul])
  map_add' x y := Subtype.ext (by show e 0 * (x + y) * e 0 = e 0 * x * e 0 + e 0 * y * e 0; ring)

@[scoped simp] theorem cornerProj_val (x : C) : (cornerProj e he x).1 = e 0 * x * e 0 := rfl

theorem cornerProj_val_self (y : Corner e he) : cornerProj e he y.1 = y := by
  apply Subtype.ext
  obtain ⟨r, hr⟩ := y.2
  show e 0 * y.1 * e 0 = y.1
  rw [← hr]
  have h := (he.idem 0).eq
  calc e 0 * (e 0 * r * e 0) * e 0 = (e 0 * e 0) * r * (e 0 * e 0) := by ring
    _ = e 0 * r * e 0 := by rw [h]

theorem cornerProj_surjective : Function.Surjective (cornerProj e he) :=
  fun y => ⟨y.1, cornerProj_val_self e he y⟩

theorem val_eq_e_mul (y : Corner e he) : y.1 = e 0 * y.1 := by
  obtain ⟨r, hr⟩ := y.2
  rw [← hr]
  have h := (he.idem 0).eq
  calc e 0 * r * e 0 = (e 0 * e 0) * r * e 0 := by rw [h]
    _ = e 0 * (e 0 * r * e 0) := by ring

def cornerCongr (ρ : C ≃+* C) (hρ : ρ (e 0) = e 0) : Corner e he ≃+* Corner e he where
  toFun y := ⟨ρ y.1, by obtain ⟨r, hr⟩ := y.2; exact ⟨ρ r, by rw [← hr, map_mul, map_mul, hρ]⟩⟩
  invFun y := ⟨ρ.symm y.1, by
    obtain ⟨r, hr⟩ := y.2
    have hρ' : ρ.symm (e 0) = e 0 := by rw [← hρ, ρ.symm_apply_apply]; exact hρ.symm ▸ rfl
    exact ⟨ρ.symm r, by rw [← hr, map_mul, map_mul, hρ']⟩⟩
  left_inv y := Subtype.ext (ρ.symm_apply_apply y.1)
  right_inv y := Subtype.ext (ρ.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul ρ x.1 y.1)
  map_add' x y := Subtype.ext (map_add ρ x.1 y.1)

@[scoped simp] theorem cornerCongr_val (ρ : C ≃+* C) (hρ : ρ (e 0) = e 0) (y : Corner e he) :
    (cornerCongr e he ρ hρ y).1 = ρ y.1 := rfl

theorem cornerProj_congr (ρ : C ≃+* C) (hρ : ρ (e 0) = e 0) (x : C) :
    cornerProj e he (ρ x) = cornerCongr e he ρ hρ (cornerProj e he x) :=
  Subtype.ext (by simp only [cornerProj_val, cornerCongr_val, map_mul, hρ])

end Corner
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

section Splitting

variable {C : Type*} [CommRing C] {d : ℕ} [NeZero d]
variable (σ : C ≃+* C) (e : ZMod d → C) (he : CompleteOrthogonalIdempotents e) (hσe : ∀ i, σ (e i) = e (i + 1))

def splittingHom : C →+* (ZMod d → Corner e he) :=
  RingHom.pi fun i => (cornerProj e he).comp ((σ ^ i.val : C ≃+* C) : C →+* C)

@[scoped simp] theorem splittingHom_apply_val (x : C) (i : ZMod d) :
    (splittingHom σ e he x i).1 = e 0 * (σ ^ i.val) x * e 0 := rfl

include hσe in
theorem splittingHom_injective : Function.Injective (splittingHom σ e he) := by
  rw [injective_iff_map_eq_zero]
  intro x hx

  have hj : ∀ j : ZMod d, e j * x = 0 := by
    intro j
    have h := congrArg Subtype.val (congrFun hx (-j))
    rw [splittingHom_apply_val] at h
    change e 0 * (σ ^ (-j).val) x * e 0 = (0 : C) at h
    have h' := congrArg (σ ^ (-j).val).symm h
    rw [map_mul, map_mul, map_zero, symm_pow_apply_e σ e hσe, RingEquiv.symm_apply_apply, zero_sub,
      ZMod.natCast_zmod_val, neg_neg] at h'

    calc e j * x = e j * e j * x := by rw [(he.idem j).eq]
      _ = e j * x * e j := by ring
      _ = 0 := h'
  calc x = (∑ j, e j) * x := by rw [he.complete, one_mul]
    _ = ∑ j, e j * x := Finset.sum_mul _ _ _
    _ = 0 := Finset.sum_eq_zero fun j _ => hj j

include hσe in
theorem splittingHom_surjective : Function.Surjective (splittingHom σ e he) := by
  intro f
  refine ⟨∑ i, (σ ^ i.val).symm (f i).1, funext fun j => ?_⟩
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
  ·
    show (cornerProj e he) ((σ ^ j.val) ((σ ^ j.val).symm (f j).1)) = f j
    rw [RingEquiv.apply_symm_apply, cornerProj_val_self]
  ·
    intro i _ hij
    apply Subtype.ext
    show e 0 * (σ ^ j.val) ((σ ^ i.val).symm (f i).1) * e 0 = 0
    rw [val_eq_e_mul e he (f i), map_mul, map_mul, symm_pow_apply_e σ e hσe, pow_apply_e σ e hσe, zero_sub,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hne : (0 : ZMod d) ≠ -i + j := fun h0 => hij (neg_add_eq_zero.mp h0.symm)
    rw [← mul_assoc (e 0), he.ortho hne, zero_mul, zero_mul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

noncomputable def splitting : C ≃+* (ZMod d → Corner e he) :=
  RingEquiv.ofBijective (splittingHom σ e he) ⟨splittingHom_injective σ e he hσe, splittingHom_surjective σ e he hσe⟩

@[scoped simp] theorem splitting_apply (x : C) : splitting σ e he hσe x = splittingHom σ e he x := rfl

end Splitting
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

section Equivariance

variable {C : Type*} [CommRing C] {d : ℕ} [NeZero d]
variable (σ : C ≃+* C) (e : ZMod d → C) (he : CompleteOrthogonalIdempotents e) (hσe : ∀ i, σ (e i) = e (i + 1))

def cornerAut : Corner e he ≃+* Corner e he :=
  cornerCongr e he (σ ^ d) (pow_d_apply_e σ e hσe 0)

@[scoped simp] theorem cornerAut_val (y : Corner e he) : (cornerAut σ e he hσe y).1 = (σ ^ d) y.1 := rfl

def cycShift (ρ : Corner e he ≃+* Corner e he) (f : ZMod d → Corner e he) : ZMod d → Corner e he :=
  fun i => if i + 1 = 0 then ρ (f (i + 1)) else f (i + 1)

include hσe in

theorem splittingHom_σ (x : C) :
    splittingHom σ e he (σ x) = cycShift e he (cornerAut σ e he hσe) (splittingHom σ e he x) := by
  funext i
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℕ, a < d ∧ ((a : ℕ) : ZMod d) = i := ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
  apply Subtype.ext
  have hsucc : ((a : ℕ) : ZMod d) + 1 = ((a + 1 : ℕ) : ZMod d) := by push_cast; rfl
  unfold cycShift
  by_cases h : a + 1 = d
  ·
    have h0 : ((a : ℕ) : ZMod d) + 1 = 0 := by rw [hsucc, h, ZMod.natCast_self]
    have hd : (σ ^ d) x = (σ ^ a) (σ x) := by rw [← h, pow_succ, RingAut.mul_apply]
    rw [if_pos h0, cornerAut_val, splittingHom_apply_val, splittingHom_apply_val, h0, ZMod.val_zero, pow_zero,
      RingAut.one_apply, map_mul, map_mul, pow_d_apply_e σ e hσe, ZMod.val_cast_of_lt ha, hd]
  · have hlt : a + 1 < d := by omega
    have h0 : ((a : ℕ) : ZMod d) + 1 ≠ 0 := by
      rw [hsucc]; intro hz
      have hv := ZMod.val_cast_of_lt hlt
      rw [hz, ZMod.val_zero] at hv
      omega
    rw [if_neg h0, splittingHom_apply_val, splittingHom_apply_val, hsucc, ZMod.val_cast_of_lt ha,
      ZMod.val_cast_of_lt hlt, pow_succ, RingAut.mul_apply]

end Equivariance
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

section Units

variable {C : Type*} [CommRing C] {d : ℕ} [NeZero d]
variable (σ : C ≃+* C) (e : ZMod d → C) (he : CompleteOrthogonalIdempotents e) (hσe : ∀ i, σ (e i) = e (i + 1))

def unitsAut : AddAut (Additive Cˣ) := MulEquiv.toAdditive (Units.mapEquiv σ.toMulEquiv)

def cornerUnitsAut : AddAut (Additive (Corner e he)ˣ) :=
  MulEquiv.toAdditive (Units.mapEquiv (cornerAut σ e he hσe).toMulEquiv)

noncomputable def unitsSplitting : Additive Cˣ ≃+ (ZMod d → Additive (Corner e he)ˣ) :=
  (MulEquiv.toAdditive ((Units.mapEquiv (splitting σ e he hσe).toMulEquiv).trans MulEquiv.piUnits)).trans
    (AddEquiv.piAdditive _)

theorem unitsAut_toMul_val (a : Additive Cˣ) : ((unitsAut σ a).toMul : C) = σ (a.toMul : C) := rfl

theorem unitsAut_pow_toMul_val (k : ℕ) (a : Additive Cˣ) :
    (((unitsAut σ ^ k) a).toMul : C) = (σ ^ k) (a.toMul : C) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => rw [pow_succ, AddAut.mul_apply', ih, unitsAut_toMul_val, pow_succ, RingAut.mul_apply]

theorem unitsAut_pow_eq_one {n : ℕ} (hσ : σ ^ n = 1) : unitsAut σ ^ n = 1 := by
  refine AddEquiv.ext fun a => ?_
  apply Additive.toMul.injective
  apply Units.ext
  rw [unitsAut_pow_toMul_val, hσ, AddAut.one_apply', RingAut.one_apply]

theorem cornerUnitsAut_toMul_val (a : Additive (Corner e he)ˣ) :
    (((cornerUnitsAut σ e he hσe a).toMul : (Corner e he)ˣ) : Corner e he).1 = (σ ^ d) ((a.toMul : Corner e he)).1 := rfl

theorem cornerUnitsAut_pow_toMul_val (k : ℕ) (a : Additive (Corner e he)ˣ) :
    ((((cornerUnitsAut σ e he hσe ^ k) a).toMul : (Corner e he)ˣ) : Corner e he).1 = (σ ^ (d * k)) ((a.toMul : Corner e he)).1 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, AddAut.mul_apply', ih, cornerUnitsAut_toMul_val, Nat.mul_succ, pow_add, RingAut.mul_apply]

theorem cornerUnitsAut_pow_eq_one {m : ℕ} (hσ : σ ^ (d * m) = 1) : cornerUnitsAut σ e he hσe ^ m = 1 := by
  refine AddEquiv.ext fun a => ?_
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  rw [cornerUnitsAut_pow_toMul_val, hσ, AddAut.one_apply', RingAut.one_apply]

theorem unitsSplitting_toMul_val (a : Additive Cˣ) (i : ZMod d) :
    (((unitsSplitting σ e he hσe a i).toMul : (Corner e he)ˣ) : Corner e he) = splittingHom σ e he (a.toMul : C) i := rfl

theorem unitsSplitting_unitsAut (a : Additive Cˣ) :
    unitsSplitting σ e he hσe (unitsAut σ a) =
      twistedShiftAut d (cornerUnitsAut σ e he hσe) (unitsSplitting σ e he hσe a) := by
  funext i
  apply Additive.toMul.injective
  apply Units.ext
  rw [unitsSplitting_toMul_val, unitsAut_toMul_val, splittingHom_σ σ e he hσe, twistedShiftAut_apply]
  unfold cycShift
  by_cases hi : i + 1 = 0
  · rw [if_pos hi, if_pos hi]
    apply Subtype.ext
    rw [cornerUnitsAut_toMul_val, unitsSplitting_toMul_val]
    rfl
  · rw [if_neg hi, if_neg hi, unitsSplitting_toMul_val]

noncomputable def unitsPair (n : ℕ) (hσ : σ ^ n = 1) : HerbrandPair (Additive Cˣ) :=
  ofAddAut (unitsAut σ) n (unitsAut_pow_eq_one σ hσ)

noncomputable def coinducedModel (m : ℕ) (hσ : σ ^ (d * m) = 1) : HerbrandPair (ZMod d → Additive (Corner e he)ˣ) :=
  @coinducedPair d m (Additive (Corner e he)ˣ) _ (cornerUnitsAut σ e he hσe) _ (cornerUnitsAut_pow_eq_one σ e he hσe hσ)

theorem coinducedModel_eq (m : ℕ) (hσ : σ ^ (d * m) = 1) :
    coinducedModel σ e he hσe m hσ =
      ofAddAut (twistedShiftAut d (cornerUnitsAut σ e he hσe)) (d * m)
        (twistedShiftAut_pow_card d m _ (cornerUnitsAut_pow_eq_one σ e he hσe hσ)) := rfl

theorem tateCard₀_units_eq_coinduced (m : ℕ) (hσ : σ ^ (d * m) = 1) :
    (unitsPair σ (d * m) hσ).tateCard₀ = (coinducedModel σ e he hσe m hσ).tateCard₀ :=
  tateCard₀_ofAddAut_congr _ _ (unitsSplitting σ e he hσe) (unitsSplitting_unitsAut σ e he hσe) _ _
    (twistedShiftAut_pow_card d m _ (cornerUnitsAut_pow_eq_one σ e he hσe hσ))

theorem tateCard₁_units_eq_coinduced (m : ℕ) (hσ : σ ^ (d * m) = 1) :
    (unitsPair σ (d * m) hσ).tateCard₁ = (coinducedModel σ e he hσe m hσ).tateCard₁ :=
  tateCard₁_ofAddAut_congr _ _ (unitsSplitting σ e he hσe) (unitsSplitting_unitsAut σ e he hσe) _ _
    (twistedShiftAut_pow_card d m _ (cornerUnitsAut_pow_eq_one σ e he hσe hσ))

end Units
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

section Shapiro

variable {C : Type*} [CommRing C] {d : ℕ} [NeZero d]
variable (σ : C ≃+* C) (e : ZMod d → C) (he : CompleteOrthogonalIdempotents e) (hσe : ∀ i, σ (e i) = e (i + 1))

noncomputable def cornerUnitsPair (m : ℕ) (hσ : σ ^ (d * m) = 1) : HerbrandPair (Additive (Corner e he)ˣ) :=
  ofAddAut (cornerUnitsAut σ e he hσe) m (cornerUnitsAut_pow_eq_one σ e he hσe hσ)

theorem tateCard₀_units_eq_corner (m : ℕ) (hσ : σ ^ (d * m) = 1) :
    (unitsPair σ (d * m) hσ).tateCard₀ = (cornerUnitsPair σ e he hσe m hσ).tateCard₀ := by
  rw [tateCard₀_units_eq_coinduced σ e he hσe m hσ]
  exact tateCard₀_coinducedPair d m _ _

theorem tateCard₁_units_eq_corner (m : ℕ) (hσ : σ ^ (d * m) = 1) :
    (unitsPair σ (d * m) hσ).tateCard₁ = (cornerUnitsPair σ e he hσe m hσ).tateCard₁ := by
  rw [tateCard₁_units_eq_coinduced σ e he hσe m hσ]
  exact tateCard₁_coinducedPair d m _ _

theorem isCohTrivial_units_iff (m : ℕ) (hσ : σ ^ (d * m) = 1) :
    IsCohTrivial (unitsPair σ (d * m) hσ) ↔ IsCohTrivial (cornerUnitsPair σ e he hσe m hσ) := by
  unfold IsCohTrivial
  rw [tateCard₀_units_eq_corner σ e he hσe m hσ, tateCard₁_units_eq_corner σ e he hσe m hσ]

end Shapiro
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

section Controls

variable (R : Type*) [CommRing R] (d : ℕ) [NeZero d]

def shiftEquiv : (ZMod d → R) ≃+* (ZMod d → R) where
  toFun f j := f (j - 1)
  invFun f j := f (j + 1)
  left_inv f := funext fun j => by show f (j + 1 - 1) = f j; rw [add_sub_cancel_right]
  right_inv f := funext fun j => by show f (j - 1 + 1) = f j; rw [sub_add_cancel]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [NeZero d] in
theorem shiftEquiv_apply (f : ZMod d → R) (j : ZMod d) : shiftEquiv R d f j = f (j - 1) := rfl

omit [NeZero d] in
theorem shiftEquiv_pow_apply (k : ℕ) (f : ZMod d → R) (j : ZMod d) : (shiftEquiv R d ^ k) f j = f (j - k) := by
  induction k generalizing f j with
  | zero => rw [pow_zero, RingAut.one_apply, Nat.cast_zero, sub_zero]
  | succ k ih => rw [pow_succ, RingAut.mul_apply, ih, shiftEquiv_apply, Nat.cast_succ, sub_sub, add_comm]

omit [NeZero d] in
theorem shiftEquiv_pow_d : shiftEquiv R d ^ (d * 1) = 1 :=
  RingEquiv.ext fun f => funext fun j => by rw [mul_one, shiftEquiv_pow_apply, ZMod.natCast_self, sub_zero]; rfl

theorem coordinate_idempotents : CompleteOrthogonalIdempotents (fun i : ZMod d => (Pi.single i 1 : ZMod d → R)) := by
  classical
  exact CompleteOrthogonalIdempotents.single (fun _ : ZMod d => R)

omit [NeZero d] in
theorem shiftEquiv_single (i : ZMod d) :
    shiftEquiv R d (Pi.single i 1) = Pi.single (i + 1) 1 := by
  classical
  funext j
  rw [shiftEquiv_apply]
  by_cases h : j = i + 1
  · subst h; rw [add_sub_cancel_right, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'; apply h; rw [← h', sub_add_cancel]

example : (unitsPair (shiftEquiv R d) (d * 1) (shiftEquiv_pow_d R d)).tateCard₀ =
    (cornerUnitsPair (shiftEquiv R d) _ (coordinate_idempotents R d) (shiftEquiv_single R d) 1
      (shiftEquiv_pow_d R d)).tateCard₀ :=
  tateCard₀_units_eq_corner _ _ _ _ _ _

example {C : Type*} [CommRing C] (e : ZMod 1 → C) (he : CompleteOrthogonalIdempotents e) : e 0 = 1 :=
  (CompleteOrthogonalIdempotents.unique_iff.mp he)

example {C : Type*} [CommRing C] (e : ZMod 1 → C) (he : CompleteOrthogonalIdempotents e) :
    Function.Injective (cornerProj e he) := fun x y h => by
  have h1 : e 0 = 1 := CompleteOrthogonalIdempotents.unique_iff.mp he
  have := congrArg Subtype.val h
  simpa only [cornerProj_val, h1, one_mul, mul_one] using this

end Controls
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

end M4aHerbrand.IdempotentCycle
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand"

end Fold_IdempotentCycleShapiro
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section Fold_HerbrandPi

set_option autoImplicit false

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace HerbrandPi
p2m_open "M4aHerbrand"

open M4aLocalCFT M4aLocalCFT.HerbrandPair M4aHerbrand.IdempotentCycle Finset

section Pi

variable {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]

noncomputable def piPair (P : ∀ i, HerbrandPair (A i)) : HerbrandPair (∀ i, A i) where
  derive :=
    { toFun := fun f i => (P i).derive (f i)
      map_zero' := funext fun i => map_zero (P i).derive
      map_add' := fun f g => funext fun i => map_add (P i).derive (f i) (g i) }
  norm :=
    { toFun := fun f i => (P i).norm (f i)
      map_zero' := funext fun i => map_zero (P i).norm
      map_add' := fun f g => funext fun i => map_add (P i).norm (f i) (g i) }
  derive_norm f := funext fun i => (P i).derive_norm (f i)
  norm_derive f := funext fun i => (P i).norm_derive (f i)

variable (P : ∀ i, HerbrandPair (A i))

theorem piPair_derive_apply (f : ∀ i, A i) (i : ι) : (piPair P).derive f i = (P i).derive (f i) := rfl

theorem piPair_norm_apply (f : ∀ i, A i) (i : ι) : (piPair P).norm f i = (P i).norm (f i) := rfl

theorem piPair_swap : (piPair P).swap = piPair fun i => (P i).swap := rfl

theorem apply_mem_ker_of_mem_ker_pi {x : ∀ i, A i} (hx : x ∈ (piPair P).derive.ker) (i : ι) :
    x i ∈ (P i).derive.ker := by
  rw [AddMonoidHom.mem_ker] at hx ⊢
  exact congrFun hx i

noncomputable def piTateCompare :
    ((piPair P).derive.ker) →+ (∀ i, ((P i).derive.ker ⧸ (P i).norm.range.addSubgroupOf (P i).derive.ker)) where
  toFun x := fun i => QuotientAddGroup.mk ⟨x.1 i, apply_mem_ker_of_mem_ker_pi P x.2 i⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem piTateCompare_surjective : Function.Surjective (piTateCompare P) := by
  intro c
  choose g hg using fun i => QuotientAddGroup.mk_surjective (c i)
  refine ⟨⟨fun i => (g i).1, ?_⟩, ?_⟩
  · rw [AddMonoidHom.mem_ker]
    funext i
    exact AddMonoidHom.mem_ker.mp (g i).2
  · funext i
    exact hg i

theorem ker_piTateCompare : (piTateCompare P).ker = (piPair P).norm.range.addSubgroupOf (piPair P).derive.ker := by
  ext x
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    have hi : ∀ i, x.1 i ∈ (P i).norm.range := by
      intro i
      have hcomp : (QuotientAddGroup.mk ⟨x.1 i, apply_mem_ker_of_mem_ker_pi P x.2 i⟩ :
          (P i).derive.ker ⧸ (P i).norm.range.addSubgroupOf (P i).derive.ker) = 0 :=
        congrFun h i
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hcomp
      exact hcomp
    choose g hg using hi
    refine ⟨g, ?_⟩
    funext i
    exact hg i
  · rintro ⟨g, hg⟩
    funext i
    show (QuotientAddGroup.mk ⟨x.1 i, apply_mem_ker_of_mem_ker_pi P x.2 i⟩ :
      (P i).derive.ker ⧸ (P i).norm.range.addSubgroupOf (P i).derive.ker) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨g i, congrFun hg i⟩

theorem tateCard₀_piPair_eq_card :
    (piPair P).tateCard₀ = Nat.card (∀ i, ((P i).derive.ker ⧸ (P i).norm.range.addSubgroupOf (P i).derive.ker)) := by
  have key := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (piTateCompare_surjective P)).toEquiv
  rw [ker_piTateCompare] at key
  exact key

theorem tateCard₀_piPair [Fintype ι] : (piPair P).tateCard₀ = ∏ i, (P i).tateCard₀ := by
  rw [tateCard₀_piPair_eq_card]
  exact Nat.card_pi

theorem tateCard₁_piPair [Fintype ι] : (piPair P).tateCard₁ = ∏ i, (P i).tateCard₁ := by
  have h := tateCard₀_piPair (fun i => (P i).swap)
  rw [← piPair_swap, tateCard₀_swap] at h
  simpa only [tateCard₀_swap] using h

theorem tateCard₀_piPair_eq_one (h : ∀ i, (P i).tateCard₀ = 1) : (piPair P).tateCard₀ = 1 := by
  rw [tateCard₀_piPair_eq_card]
  have hi : ∀ i, Subsingleton ((P i).derive.ker ⧸ (P i).norm.range.addSubgroupOf (P i).derive.ker) ∧
      Nonempty ((P i).derive.ker ⧸ (P i).norm.range.addSubgroupOf (P i).derive.ker) :=
    fun i => Nat.card_eq_one_iff_unique.mp (h i)
  haveI : ∀ i, Subsingleton ((P i).derive.ker ⧸ (P i).norm.range.addSubgroupOf (P i).derive.ker) := fun i => (hi i).1
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨fun _ => 0⟩⟩

theorem tateCard₁_piPair_eq_one (h : ∀ i, (P i).tateCard₁ = 1) : (piPair P).tateCard₁ = 1 := by
  have h' := tateCard₀_piPair_eq_one (fun i => (P i).swap) (fun i => by rw [tateCard₀_swap]; exact h i)
  rwa [← piPair_swap, tateCard₀_swap] at h'

end Pi
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section PiAut

variable {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)] (α : ∀ i, AddAut (A i))

theorem piCongrRight_pow_apply (k : ℕ) (f : ∀ i, A i) (i : ι) :
    (AddEquiv.piCongrRight α ^ k) f i = (α i ^ k) (f i) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AddAut.mul_apply', AddAut.mul_apply', ih]; rfl

theorem piCongrRight_pow_eq_one {n : ℕ} (hα : ∀ i, α i ^ n = 1) : AddEquiv.piCongrRight α ^ n = 1 := by
  refine AddEquiv.ext fun f => funext fun i => ?_
  rw [piCongrRight_pow_apply, hα i]
  rfl

theorem tateCard₀_ofAddAut_piCongrRight (n : ℕ) (hα : ∀ i, α i ^ n = 1) (h : AddEquiv.piCongrRight α ^ n = 1) :
    (ofAddAut (AddEquiv.piCongrRight α) n h).tateCard₀ = (piPair fun i => ofAddAut (α i) n (hα i)).tateCard₀ := by
  refine tateCard₀_congr _ _ (AddEquiv.refl _) (fun f => ?_) (fun f => ?_)
  · rfl
  · show (piPair fun i => ofAddAut (α i) n (hα i)).norm f = (ofAddAut (AddEquiv.piCongrRight α) n h).norm f
    funext i
    rw [piPair_norm_apply, ofAddAut_norm_apply, ofAddAut_norm_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => (piCongrRight_pow_apply α k f i).symm

theorem tateCard₁_ofAddAut_piCongrRight (n : ℕ) (hα : ∀ i, α i ^ n = 1) (h : AddEquiv.piCongrRight α ^ n = 1) :
    (ofAddAut (AddEquiv.piCongrRight α) n h).tateCard₁ = (piPair fun i => ofAddAut (α i) n (hα i)).tateCard₁ := by
  refine tateCard₁_congr _ _ (AddEquiv.refl _) (fun f => ?_) (fun f => ?_)
  · rfl
  · show (piPair fun i => ofAddAut (α i) n (hα i)).norm f = (ofAddAut (AddEquiv.piCongrRight α) n h).norm f
    funext i
    rw [piPair_norm_apply, ofAddAut_norm_apply, ofAddAut_norm_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => (piCongrRight_pow_apply α k f i).symm

end PiAut
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section ProdAut

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] (α : AddAut A) (β : AddAut B)

theorem prodCongr_pow_apply (k : ℕ) (z : A × B) : (α.prodCongr β ^ k) z = ((α ^ k) z.1, (β ^ k) z.2) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, pow_succ, AddAut.mul_apply', AddAut.mul_apply', AddAut.mul_apply', ih]; rfl

theorem prodCongr_pow_eq_one {n : ℕ} (hα : α ^ n = 1) (hβ : β ^ n = 1) : α.prodCongr β ^ n = 1 := by
  refine AddEquiv.ext fun z => ?_
  rw [prodCongr_pow_apply, hα, hβ]
  rfl

theorem tateCard₀_ofAddAut_prodCongr (n : ℕ) (hα : α ^ n = 1) (hβ : β ^ n = 1) (h : α.prodCongr β ^ n = 1) :
    (ofAddAut (α.prodCongr β) n h).tateCard₀ = ((ofAddAut α n hα).prod (ofAddAut β n hβ)).tateCard₀ := by
  refine tateCard₀_congr _ _ (AddEquiv.refl _) (fun z => ?_) (fun z => ?_)
  · rfl
  · show ((ofAddAut α n hα).norm z.1, (ofAddAut β n hβ).norm z.2) = (ofAddAut (α.prodCongr β) n h).norm z
    rw [ofAddAut_norm_apply, ofAddAut_norm_apply, ofAddAut_norm_apply, Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · show ∑ k ∈ range n, (α ^ k) z.1 = (∑ k ∈ range n, (α.prodCongr β ^ k) z).1
      rw [Prod.fst_sum]; exact Finset.sum_congr rfl fun k _ => (congrArg Prod.fst (prodCongr_pow_apply α β k z)).symm
    · show ∑ k ∈ range n, (β ^ k) z.2 = (∑ k ∈ range n, (α.prodCongr β ^ k) z).2
      rw [Prod.snd_sum]; exact Finset.sum_congr rfl fun k _ => (congrArg Prod.snd (prodCongr_pow_apply α β k z)).symm

theorem tateCard₁_ofAddAut_prodCongr (n : ℕ) (hα : α ^ n = 1) (hβ : β ^ n = 1) (h : α.prodCongr β ^ n = 1) :
    (ofAddAut (α.prodCongr β) n h).tateCard₁ = ((ofAddAut α n hα).prod (ofAddAut β n hβ)).tateCard₁ := by
  refine tateCard₁_congr _ _ (AddEquiv.refl _) (fun z => ?_) (fun z => ?_)
  · rfl
  · show ((ofAddAut α n hα).norm z.1, (ofAddAut β n hβ).norm z.2) = (ofAddAut (α.prodCongr β) n h).norm z
    rw [ofAddAut_norm_apply, ofAddAut_norm_apply, ofAddAut_norm_apply, Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · show ∑ k ∈ range n, (α ^ k) z.1 = (∑ k ∈ range n, (α.prodCongr β ^ k) z).1
      rw [Prod.fst_sum]; exact Finset.sum_congr rfl fun k _ => (congrArg Prod.fst (prodCongr_pow_apply α β k z)).symm
    · show ∑ k ∈ range n, (β ^ k) z.2 = (∑ k ∈ range n, (α.prodCongr β ^ k) z).2
      rw [Prod.snd_sum]; exact Finset.sum_congr rfl fun k _ => (congrArg Prod.snd (prodCongr_pow_apply α β k z)).symm

end ProdAut
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end M4aHerbrand.HerbrandPi
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section Battery
#print axioms M4aHerbrand.HerbrandPi.piPair
#print axioms M4aHerbrand.HerbrandPi.tateCard₀_piPair
#print axioms M4aHerbrand.HerbrandPi.tateCard₁_piPair
#print axioms M4aHerbrand.HerbrandPi.tateCard₀_piPair_eq_one
#print axioms M4aHerbrand.HerbrandPi.tateCard₁_piPair_eq_one
#print axioms M4aHerbrand.HerbrandPi.piCongrRight_pow_eq_one
#print axioms M4aHerbrand.HerbrandPi.tateCard₀_ofAddAut_piCongrRight
#print axioms M4aHerbrand.HerbrandPi.tateCard₁_ofAddAut_piCongrRight
#print axioms M4aHerbrand.HerbrandPi.prodCongr_pow_eq_one
#print axioms M4aHerbrand.HerbrandPi.tateCard₀_ofAddAut_prodCongr
#print axioms M4aHerbrand.HerbrandPi.tateCard₁_ofAddAut_prodCongr

example : (M4aHerbrand.HerbrandPi.piPair (fun _ : Fin 3 =>
    M4aLocalCFT.HerbrandPair.ofAddAut (1 : AddAut ℤ) 1 (pow_one _))).tateCard₁ = 1 :=
  M4aHerbrand.HerbrandPi.tateCard₁_piPair_eq_one _ fun _ =>
    (M4aLocalCFT.SemilocalHerbrand.isCohTrivial_ofAddAut_one (1 : AddAut ℤ) (pow_one _)).2
end Battery
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end Fold_HerbrandPi
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section Fold_LocalDegreeProd

set_option autoImplicit false

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace LocalDegree
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

noncomputable def finSplit (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}

noncomputable def infSplit (v : InfinitePlace K) : ℕ :=
  Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}

variable [NumberField K]

noncomputable def localDegreeProd (S : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  (∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / finSplit K L v) * ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / infSplit K L v

theorem localDegreeProd_def (S : Finset (HeightOneSpectrum (𝓞 K))) :
    localDegreeProd K L S =
      (∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / finSplit K L v) * ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / infSplit K L v :=
  rfl

omit [NumberField K] in
theorem finSplit_def (v : HeightOneSpectrum (𝓞 K)) :
    finSplit K L v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} := rfl

omit [NumberField K] in
theorem infSplit_def (v : InfinitePlace K) :
    infSplit K L v = Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v} := rfl

end M4aHerbrand.LocalDegree
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section Battery
open M4aHerbrand.LocalDegree
#print axioms localDegreeProd_def
#print axioms finSplit_def
#print axioms infSplit_def
end Battery
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section ed19Prints
open M4aHerbrand.LocalDegree
set_option pp.deepTerms true in
set_option pp.funBinderTypes true in
#check @localDegreeProd
#print localDegreeProd
end ed19Prints
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end Fold_LocalDegreeProd
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section Fold_OrbitPlaces

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
p2m_open "M4aHerbrand"

p2m_open "Ideal MulAction IsDedekindDomain Ideal.IsDedekindDomain"

noncomputable section

section Fibre

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  (p : Ideal A)

theorem subsingleton_orbitQuotient_primesOver :
    Subsingleton (orbitRel.Quotient G (primesOver p B)) := by
  constructor
  refine Quotient.ind₂ ?_
  intro a b
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G b a
  exact Quotient.sound ⟨σ, hσ⟩

theorem natCard_orbitQuotient_primesOver_eq_one
    [IsDomain A] [Nontrivial B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [p.IsPrime] :
    Nat.card (orbitRel.Quotient G (primesOver p B)) = 1 := by
  haveI := subsingleton_orbitQuotient_primesOver (B := B) G p
  haveI hne : Nonempty (primesOver p B) := inferInstance
  haveI : Nonempty (orbitRel.Quotient G (primesOver p B)) :=
    ⟨Quotient.mk (orbitRel G (primesOver p B)) hne.some⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

def primesOverEquivQuotientStabilizer (w₀ : primesOver p B) :
    (primesOver p B) ≃ G ⧸ MulAction.stabilizer G w₀ :=
  ((Equiv.Set.univ _).symm.trans
    (Equiv.setCongr (MulAction.orbit_eq_univ G w₀).symm)).trans
    (MulAction.orbitEquivQuotientStabilizer G w₀)

end Fibre
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section DedekindBridge

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]

def underPlace (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.under A
  isPrime := by haveI := w.isPrime; infer_instance
  ne_bot := w.asIdeal.under_ne_bot A w.ne_bot

omit [FaithfulSMul A B] in
@[scoped simp] theorem underPlace_asIdeal (w : HeightOneSpectrum B) :
    (underPlace (A := A) w).asIdeal = w.asIdeal.under A :=
  rfl

def finitePlacesOver (S' : Set (HeightOneSpectrum A)) : Set (HeightOneSpectrum B) :=
  {w | underPlace (A := A) w ∈ S'}

omit [FaithfulSMul A B] in
theorem mem_finitePlacesOver {S' : Set (HeightOneSpectrum A)} {w : HeightOneSpectrum B} :
    w ∈ finitePlacesOver (B := B) S' ↔ underPlace (A := A) w ∈ S' :=
  Iff.rfl

def placeOfPrimesOver (v : HeightOneSpectrum A) (Q : primesOver v.asIdeal B) :
    HeightOneSpectrum B where
  asIdeal := Q.1
  isPrime := Q.2.1
  ne_bot := by
    rintro hbot
    apply v.ne_bot
    have hover : v.asIdeal = Q.1.under A := Q.2.2.over
    rw [hover, hbot, under_def, Ideal.comap_bot_of_injective (algebraMap A B)
      (FaithfulSMul.algebraMap_injective A B)]

def fiberEquivPrimesOver (S' : Set (HeightOneSpectrum A)) (v : S') :
    {w : finitePlacesOver (B := B) S' //
        (⟨underPlace (A := A) w.1, w.2⟩ : S') = v}
      ≃ primesOver (v : HeightOneSpectrum A).asIdeal B where
  toFun w :=
    ⟨w.1.1.asIdeal, w.1.1.isPrime, ⟨by
      have h : underPlace (A := A) w.1.1 = (v : HeightOneSpectrum A) :=
        congrArg Subtype.val w.2
      rw [← h]
      rfl⟩⟩
  invFun Q :=
    ⟨⟨placeOfPrimesOver (A := A) (v : HeightOneSpectrum A) Q, by
        rw [mem_finitePlacesOver]
        have hu : underPlace (A := A)
            (placeOfPrimesOver (A := A) (v : HeightOneSpectrum A) Q)
            = (v : HeightOneSpectrum A) :=
          HeightOneSpectrum.ext (by rw [underPlace_asIdeal]; exact Q.2.2.over.symm)
        rw [hu]
        exact v.2⟩,
      Subtype.ext (HeightOneSpectrum.ext
        (by rw [underPlace_asIdeal]; exact Q.2.2.over.symm))⟩
  left_inv w := Subtype.ext (Subtype.ext (HeightOneSpectrum.ext rfl))
  right_inv Q := Subtype.ext rfl

def finitePlacesOverEquivSigma (S' : Set (HeightOneSpectrum A)) :
    finitePlacesOver (B := B) S' ≃ Σ v : S', primesOver (v : HeightOneSpectrum A).asIdeal B :=
  ((Equiv.sigmaFiberEquiv
      (fun w : finitePlacesOver (B := B) S' =>
        (⟨underPlace (A := A) w.1, w.2⟩ : S'))).symm).trans
    (Equiv.sigmaCongrRight fun v => fiberEquivPrimesOver (B := B) S' v)

end DedekindBridge
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end M4aHerbrand
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end Fold_OrbitPlaces
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section Fold_OrbitCount

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
p2m_open "M4aHerbrand"

p2m_open "Ideal MulAction IsDedekindDomain Ideal.IsDedekindDomain"

open scoped Pointwise

noncomputable section

section PlacesAction

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

scoped instance instMulActionPlaces : MulAction G (HeightOneSpectrum B) where
  smul σ w :=
    { asIdeal := σ • w.asIdeal
      isPrime := by haveI := w.isPrime; infer_instance
      ne_bot := fun hbot => w.ne_bot (by
        have h : σ⁻¹ • σ • w.asIdeal = σ⁻¹ • (⊥ : Ideal B) := by rw [hbot]
        rwa [inv_smul_smul, Ideal.pointwise_smul_def, Ideal.map_bot] at h) }
  one_smul w := HeightOneSpectrum.ext (one_smul G w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)

omit [IsDomain B] [Finite G] in
@[scoped simp] theorem smul_place_asIdeal (σ : G) (w : HeightOneSpectrum B) :
    (σ • w).asIdeal = σ • w.asIdeal :=
  rfl

omit [FaithfulSMul A B] [Module.IsTorsionFree A B] [Finite G] in
theorem underPlace_smul (σ : G) (w : HeightOneSpectrum B) :
    underPlace (A := A) (σ • w) = underPlace (A := A) w :=
  HeightOneSpectrum.ext (Ideal.under_smul A w.asIdeal σ)

scoped instance instMulActionFinitePlacesOver (S' : Set (HeightOneSpectrum A)) :
    MulAction G ↥(finitePlacesOver (B := B) S') where
  smul σ w := ⟨σ • w.1, by
    show underPlace (A := A) (σ • w.1) ∈ S'
    rw [underPlace_smul]
    exact w.2⟩
  one_smul w := Subtype.ext (one_smul G w.1)
  mul_smul σ τ w := Subtype.ext (mul_smul σ τ w.1)

omit [FaithfulSMul A B] [Module.IsTorsionFree A B] [Finite G] in
@[scoped simp] theorem smul_finitePlacesOver_coe (S' : Set (HeightOneSpectrum A)) (σ : G)
    (w : ↥(finitePlacesOver (B := B) S')) :
    ((σ • w : ↥(finitePlacesOver (B := B) S')) : HeightOneSpectrum B) = σ • (w : HeightOneSpectrum B) :=
  rfl

noncomputable def orbitQuotientFinitePlacesOverEquiv (S' : Set (HeightOneSpectrum A)) :
    orbitRel.Quotient G ↥(finitePlacesOver (B := B) S') ≃ ↥S' := by
  refine Equiv.ofBijective
    (Quotient.lift
      (fun w : ↥(finitePlacesOver (B := B) S') =>
        (⟨underPlace (A := A) w.1, w.2⟩ : ↥S')) ?_) ⟨?_, ?_⟩
  · rintro w₁ w₂ h
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    subst hσ
    exact Subtype.ext (underPlace_smul (A := A) G σ w₂.1)
  · intro qa qb
    refine Quotient.inductionOn₂ qa qb ?_
    intro w₁ w₂ hf
    have hv : underPlace (A := A) w₁.1 = underPlace (A := A) w₂.1 :=
      congrArg Subtype.val hf
    have hQ₁ : w₁.1.asIdeal ∈
        ((underPlace (A := A) w₂.1).asIdeal.primesOver B : Set (Ideal B)) := by
      refine ⟨w₁.1.isPrime, ⟨?_⟩⟩
      rw [← hv]
      rfl
    have hQ₂ : w₂.1.asIdeal ∈
        ((underPlace (A := A) w₂.1).asIdeal.primesOver B : Set (Ideal B)) :=
      ⟨w₂.1.isPrime, ⟨rfl⟩⟩
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G
      (⟨w₂.1.asIdeal, hQ₂⟩ : (underPlace (A := A) w₂.1).asIdeal.primesOver B)
      ⟨w₁.1.asIdeal, hQ₁⟩
    have hσ' : σ • w₂.1.asIdeal = w₁.1.asIdeal := by
      have h := congrArg Subtype.val hσ
      rwa [Ideal.coe_smul_primesOver] at h
    refine Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
      ⟨σ, ?_⟩))
    exact Subtype.ext (HeightOneSpectrum.ext hσ')
  · intro v
    obtain ⟨Q⟩ :=
      (inferInstance : Nonempty ((v : HeightOneSpectrum A).asIdeal.primesOver B))
    have hu : underPlace (A := A)
        (placeOfPrimesOver (A := A) (v : HeightOneSpectrum A) Q)
        = (v : HeightOneSpectrum A) :=
      HeightOneSpectrum.ext (by rw [underPlace_asIdeal]; exact Q.2.2.over.symm)
    refine ⟨Quotient.mk _
      ⟨placeOfPrimesOver (A := A) (v : HeightOneSpectrum A) Q, ?_⟩, ?_⟩
    · show underPlace (A := A)
        (placeOfPrimesOver (A := A) (v : HeightOneSpectrum A) Q) ∈ S'
      rw [hu]
      exact v.2
    · exact Subtype.ext hu

theorem natCard_orbitQuotient_finitePlacesOver (S' : Set (HeightOneSpectrum A)) :
    Nat.card (orbitRel.Quotient G ↥(finitePlacesOver (B := B) S')) = Nat.card ↥S' :=
  Nat.card_congr (orbitQuotientFinitePlacesOverEquiv (A := A) (B := B) G S')

end PlacesAction
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end M4aHerbrand
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end Fold_OrbitCount
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section Fold_PlacePermLattice

set_option autoImplicit false

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace PermLattice
p2m_open "M4aHerbrand"

open M4aLocalCFT M4aLocalCFT.HerbrandPair M4aLocalCFT.SemilocalHerbrand M4aLocalCFT.LocalUnitsCohomology
open M4aHerbrand.IdempotentCycle M4aHerbrand.HerbrandPi Finset

section Generic

variable {X : Type*}

def permLatticeAut (π : Equiv.Perm X) : AddAut (X → ℤ) where
  toFun f := fun x => f (π.symm x)
  invFun f := fun x => f (π x)
  left_inv f := funext fun x => congrArg f (π.symm_apply_apply x)
  right_inv f := funext fun x => congrArg f (π.apply_symm_apply x)
  map_add' _ _ := rfl

@[scoped simp] theorem permLatticeAut_apply (π : Equiv.Perm X) (f : X → ℤ) (x : X) :
    permLatticeAut π f x = f (π.symm x) := rfl

theorem permLatticeAut_mul (π ρ : Equiv.Perm X) :
    permLatticeAut (π * ρ) = permLatticeAut π * permLatticeAut ρ :=
  AddEquiv.ext fun _ => funext fun _ => rfl

theorem permLatticeAut_one : permLatticeAut (1 : Equiv.Perm X) = 1 :=
  AddEquiv.ext fun _ => funext fun _ => rfl

def permLatticeAutHom : Equiv.Perm X →* AddAut (X → ℤ) where
  toFun := permLatticeAut
  map_one' := permLatticeAut_one
  map_mul' := permLatticeAut_mul

@[scoped simp] theorem permLatticeAutHom_apply (π : Equiv.Perm X) : permLatticeAutHom π = permLatticeAut π := rfl

theorem permLatticeAut_pow (π : Equiv.Perm X) (k : ℕ) : permLatticeAut π ^ k = permLatticeAut (π ^ k) := by
  rw [← permLatticeAutHom_apply, ← map_pow, permLatticeAutHom_apply]

theorem permLatticeAut_pow_eq_one {π : Equiv.Perm X} {n : ℕ} (hπ : π ^ n = 1) : permLatticeAut π ^ n = 1 := by
  rw [permLatticeAut_pow, hπ, permLatticeAut_one]

def permLatticePair (π : Equiv.Perm X) (n : ℕ) (hπ : π ^ n = 1) : HerbrandPair (X → ℤ) :=
  HerbrandPair.ofAddAut (permLatticeAut π) n (permLatticeAut_pow_eq_one hπ)

theorem permLatticePair_def (π : Equiv.Perm X) (n : ℕ) (hπ : π ^ n = 1) :
    permLatticePair π n hπ = HerbrandPair.ofAddAut (permLatticeAut π) n (permLatticeAut_pow_eq_one hπ) := rfl

theorem ofAddAut_exp_congr {A : Type*} [AddCommGroup A] (α : AddAut A) {n n' : ℕ} (h : n = n')
    (hn : α ^ n = 1) (hn' : α ^ n' = 1) : HerbrandPair.ofAddAut α n hn = HerbrandPair.ofAddAut α n' hn' := by
  subst h; rfl

theorem twistedShiftAut_one_apply (d : ℕ) (g : ZMod d → ℤ) (i : ZMod d) :
    twistedShiftAut d (1 : AddAut ℤ) g i = g (i + 1) := by
  rw [twistedShiftAut_apply]
  split_ifs <;> rfl

theorem tateCard_permLatticePair_of_isCycleOn [Finite X] [Nonempty X] (π : Equiv.Perm X)
    (hcyc : π.IsCycleOn Set.univ) {n : ℕ} (hπ : π ^ n = 1) (hn : n ≠ 0) :
    (permLatticePair π n hπ).tateCard₀ = n / Nat.card X ∧ (permLatticePair π n hπ).tateCard₁ = 1 := by
  classical
  haveI := Fintype.ofFinite X
  obtain ⟨x₀⟩ := ‹Nonempty X›

  have hφ : (π⁻¹).IsCycleOn ((Finset.univ : Finset X) : Set X) := by
    rw [Finset.coe_univ]; exact hcyc.inv
  have hφn : π⁻¹ ^ n = 1 := by rw [inv_pow, hπ, inv_one]
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have hx₀ : x₀ ∈ (Finset.univ : Finset X) := Finset.mem_univ x₀
  have hcardu : (Finset.univ : Finset X).card = Fintype.card X := Finset.card_univ

  have hdn : Fintype.card X ∣ n := by
    have h := (hφ.pow_apply_eq hx₀ (n := n)).1 (by rw [hφn]; rfl)
    rwa [hcardu] at h
  obtain ⟨m, hm⟩ := hdn
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by rw [hm, Nat.mul_zero])
  have hmdiv : n / Nat.card X = m := by
    rw [Nat.card_eq_fintype_card, hm, Nat.mul_div_cancel_left _ (NeZero.pos (Fintype.card X))]

  have hper : ∀ k : ℕ, (π⁻¹ ^ (k % Fintype.card X)) x₀ = (π⁻¹ ^ k) x₀ := fun k =>
    (hφ.pow_apply_eq_pow_apply hx₀).2 (by rw [hcardu]; exact Nat.mod_modEq k _)
  have he_inj : Function.Injective fun i : ZMod (Fintype.card X) => (π⁻¹ ^ i.val) x₀ := by
    intro i j h
    have h' := (hφ.pow_apply_eq_pow_apply hx₀).1 h
    rw [hcardu] at h'
    exact ZMod.val_injective _ (Nat.ModEq.eq_of_lt_of_lt h' (ZMod.val_lt i) (ZMod.val_lt j))
  have he_bij : Function.Bijective fun i : ZMod (Fintype.card X) => (π⁻¹ ^ i.val) x₀ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨he_inj, by rw [ZMod.card]⟩
  let ε : ZMod (Fintype.card X) ≃ X := Equiv.ofBijective _ he_bij
  have hε : ∀ i : ZMod (Fintype.card X), π⁻¹ (ε i) = ε (i + 1) := by
    intro i
    show π⁻¹ ((π⁻¹ ^ i.val) x₀) = (π⁻¹ ^ (i + 1).val) x₀
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod, hper, pow_succ', Equiv.Perm.mul_apply]

  let Φ : (X → ℤ) ≃+ (ZMod (Fintype.card X) → ℤ) :=
    { toFun := fun g i => g (ε i)
      invFun := fun h x => h (ε.symm x)
      left_inv := fun g => funext fun x => by simp only [Equiv.apply_symm_apply]
      right_inv := fun h => funext fun i => by simp only [Equiv.symm_apply_apply]
      map_add' := fun _ _ => rfl }
  have hΦ : ∀ g : X → ℤ, Φ (permLatticeAut π g) = twistedShiftAut (Fintype.card X) (1 : AddAut ℤ) (Φ g) := by
    intro g
    funext i
    show g (π.symm (ε i)) = twistedShiftAut (Fintype.card X) (1 : AddAut ℤ) (fun j => g (ε j)) i
    rw [twistedShiftAut_one_apply, ← hε]
    rfl
  have hT : twistedShiftAut (Fintype.card X) (1 : AddAut ℤ) ^ n = 1 := by
    rw [hm]; exact twistedShiftAut_pow_card _ m (1 : AddAut ℤ) (one_pow m)
  have key : HerbrandPair.ofAddAut (twistedShiftAut (Fintype.card X) (1 : AddAut ℤ)) n hT
      = coinducedPair (Fintype.card X) m (1 : AddAut ℤ) (one_pow m) :=
    ofAddAut_exp_congr _ hm _ _
  refine ⟨?_, ?_⟩
  · calc (permLatticePair π n hπ).tateCard₀
        = (HerbrandPair.ofAddAut (twistedShiftAut (Fintype.card X) (1 : AddAut ℤ)) n hT).tateCard₀ :=
          tateCard₀_ofAddAut_congr _ _ Φ hΦ n _ hT
      _ = (coinducedPair (Fintype.card X) m (1 : AddAut ℤ) (one_pow m)).tateCard₀ := by rw [key]
      _ = m := tateCard₀_coinducedPair_int _ m hm0
      _ = n / Nat.card X := hmdiv.symm
  · calc (permLatticePair π n hπ).tateCard₁
        = (HerbrandPair.ofAddAut (twistedShiftAut (Fintype.card X) (1 : AddAut ℤ)) n hT).tateCard₁ :=
          tateCard₁_ofAddAut_congr _ _ Φ hΦ n _ hT
      _ = (coinducedPair (Fintype.card X) m (1 : AddAut ℤ) (one_pow m)).tateCard₁ := by rw [key]
      _ = (HerbrandPair.ofAddAut (1 : AddAut ℤ) m (one_pow m)).tateCard₁ := tateCard₁_coinducedPair _ m _ _
      _ = 1 := tateCard₁_intCyclicPair hm0

theorem subtypePerm_pow_apply_coe {p : X → Prop} (π : Equiv.Perm X) (h : ∀ x, p (π x) ↔ p x) (k : ℕ)
    (x : {x // p x}) : ((π.subtypePerm h ^ k) x : X) = (π ^ k) (x : X) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]; rfl

theorem tateCard_permLatticePair_fibration {Y : Type*} [Finite X] [Fintype Y] (f : X → Y)
    (hf : Function.Surjective f) (π : Equiv.Perm X) (hcyc : ∀ y, π.IsCycleOn {x | f x = y})
    {n : ℕ} (hπ : π ^ n = 1) (hn : n ≠ 0) :
    (permLatticePair π n hπ).tateCard₀ = ∏ y, n / Nat.card {x // f x = y}
      ∧ (permLatticePair π n hπ).tateCard₁ = 1 := by

  have hmem : ∀ (y : Y) (x : X), f (π x) = y ↔ f x = y := fun y _ => (hcyc y).apply_mem_iff
  let πf : ∀ y : Y, Equiv.Perm {x // f x = y} := fun y => π.subtypePerm (hmem y)
  have hπf_cyc : ∀ y, (πf y).IsCycleOn Set.univ := fun y => (hcyc y).subtypePerm
  have hπf_pow : ∀ y, πf y ^ n = 1 := fun y =>
    Equiv.ext fun x => Subtype.ext (by rw [subtypePerm_pow_apply_coe, hπ]; rfl)
  have hfib : ∀ y, (permLatticePair (πf y) n (hπf_pow y)).tateCard₀ = n / Nat.card {x // f x = y}
      ∧ (permLatticePair (πf y) n (hπf_pow y)).tateCard₁ = 1 := by
    intro y
    haveI : Nonempty {x // f x = y} := let ⟨x, hx⟩ := hf y; ⟨⟨x, hx⟩⟩
    exact tateCard_permLatticePair_of_isCycleOn (πf y) (hπf_cyc y) (hπf_pow y) hn

  let Φ : (X → ℤ) ≃+ (∀ y : Y, ({x // f x = y} → ℤ)) :=
    { toFun := fun g y x => g x.1
      invFun := fun G x => G (f x) ⟨x, rfl⟩
      left_inv := fun g => rfl
      right_inv := fun G => by
        funext y x
        rcases x with ⟨x, rfl⟩
        rfl
      map_add' := fun _ _ => rfl }
  have hΦ : ∀ g, Φ (permLatticeAut π g) = AddEquiv.piCongrRight (fun y => permLatticeAut (πf y)) (Φ g) :=
    fun g => rfl
  have hα : ∀ y, permLatticeAut (πf y) ^ n = 1 := fun y => permLatticeAut_pow_eq_one (hπf_pow y)
  have hB : AddEquiv.piCongrRight (fun y => permLatticeAut (πf y)) ^ n = 1 := piCongrRight_pow_eq_one _ hα
  refine ⟨?_, ?_⟩
  · calc (permLatticePair π n hπ).tateCard₀
        = (HerbrandPair.ofAddAut (AddEquiv.piCongrRight fun y => permLatticeAut (πf y)) n hB).tateCard₀ :=
          tateCard₀_ofAddAut_congr _ _ Φ hΦ n _ hB
      _ = (piPair fun y => HerbrandPair.ofAddAut (permLatticeAut (πf y)) n (hα y)).tateCard₀ :=
          tateCard₀_ofAddAut_piCongrRight _ n hα hB
      _ = ∏ y, (HerbrandPair.ofAddAut (permLatticeAut (πf y)) n (hα y)).tateCard₀ := tateCard₀_piPair _
      _ = ∏ y, n / Nat.card {x // f x = y} := Finset.prod_congr rfl fun y _ => (hfib y).1
  · calc (permLatticePair π n hπ).tateCard₁
        = (HerbrandPair.ofAddAut (AddEquiv.piCongrRight fun y => permLatticeAut (πf y)) n hB).tateCard₁ :=
          tateCard₁_ofAddAut_congr _ _ Φ hΦ n _ hB
      _ = (piPair fun y => HerbrandPair.ofAddAut (permLatticeAut (πf y)) n (hα y)).tateCard₁ :=
          tateCard₁_ofAddAut_piCongrRight _ n hα hB
      _ = ∏ y, (HerbrandPair.ofAddAut (permLatticeAut (πf y)) n (hα y)).tateCard₁ := tateCard₁_piPair _
      _ = ∏ _y : Y, (1 : ℕ) := Finset.prod_congr rfl fun y _ => (hfib y).2
      _ = 1 := Finset.prod_const_one

end Generic
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

section GroupForm

variable {G X Y : Type*} [Group G] [Finite G]

theorem isCycleOn_fibre_of_generator (ρ : G →* Equiv.Perm X) (σ : G) (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)
    (f : X → Y) (hinv : ∀ (τ : G) (x : X), f (ρ τ x) = f x)
    (htrans : ∀ x x' : X, f x = f x' → ∃ τ : G, ρ τ x = x') (y : Y) :
    (ρ σ).IsCycleOn {x | f x = y} := by
  refine ⟨⟨fun x hx => ?_, (ρ σ).injective.injOn, fun x hx => ?_⟩, fun x hx x' hx' => ?_⟩
  · show f (ρ σ x) = y
    rw [hinv]; exact hx
  · refine ⟨ρ σ⁻¹ x, ?_, ?_⟩
    · show f (ρ σ⁻¹ x) = y
      rw [hinv]; exact hx
    · show ρ σ (ρ σ⁻¹ x) = x
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  · obtain ⟨τ, hτ⟩ := htrans x x' (hx.trans hx'.symm)
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hσ τ))
    exact ⟨k, by rw [zpow_natCast, ← map_pow]; exact hτ⟩

omit [Finite G] in
theorem map_pow_natCard_eq_one (ρ : G →* Equiv.Perm X) (σ : G) : ρ σ ^ Nat.card G = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem tateCard_permLatticePair_of_generator [Finite X] [Fintype Y] (ρ : G →* Equiv.Perm X) (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (f : X → Y) (hf : Function.Surjective f)
    (hinv : ∀ (τ : G) (x : X), f (ρ τ x) = f x) (htrans : ∀ x x' : X, f x = f x' → ∃ τ : G, ρ τ x = x') :
    (permLatticePair (ρ σ) (Nat.card G) (map_pow_natCard_eq_one ρ σ)).tateCard₀
        = ∏ y, Nat.card G / Nat.card {x // f x = y}
      ∧ (permLatticePair (ρ σ) (Nat.card G) (map_pow_natCard_eq_one ρ σ)).tateCard₁ = 1 := by
  haveI : Nonempty G := ⟨σ⟩
  exact tateCard_permLatticePair_fibration f hf (ρ σ) (isCycleOn_fibre_of_generator ρ σ hσ f hinv htrans)
    (map_pow_natCard_eq_one ρ σ) Nat.card_pos.ne'

end GroupForm
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

end M4aHerbrand.PermLattice
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace PlacePermLattice
p2m_open "M4aHerbrand"

p2m_open "NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.LocalDegree"
open M4aLocalCFT M4aLocalCFT.HerbrandPair
open scoped Pointwise

section FinitePlaces

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem place_under_smul (τ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : (τ • w).under (𝓞 K) = w.under (𝓞 K) :=
  HeightOneSpectrum.ext (Ideal.under_smul (𝓞 K) w.asIdeal τ)

def galPermSL (S : Set (HeightOneSpectrum (𝓞 K))) :
    (L ≃ₐ[K] L) →* Equiv.Perm ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S} where
  toFun τ := (MulAction.toPerm τ).subtypePerm fun w => by
    show (τ • w).under (𝓞 K) ∈ S ↔ w.under (𝓞 K) ∈ S
    rw [place_under_smul]
  map_one' := Equiv.ext fun w => Subtype.ext (one_smul _ w.1)
  map_mul' τ τ' := Equiv.ext fun w => Subtype.ext (mul_smul τ τ' w.1)

@[scoped simp] theorem galPermSL_apply_coe (S : Set (HeightOneSpectrum (𝓞 K))) (τ : L ≃ₐ[K] L)
    (w : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}) : ((galPermSL K L S τ w : _) : HeightOneSpectrum (𝓞 L)) = τ • w.1 :=
  rfl

@[scoped simp] theorem galPermSL_symm_apply_coe (S : Set (HeightOneSpectrum (𝓞 K))) (τ : L ≃ₐ[K] L)
    (w : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}) :
    (((galPermSL K L S τ).symm w : _) : HeightOneSpectrum (𝓞 L)) = τ⁻¹ • w.1 :=
  rfl

def placePermAut (σ : L ≃ₐ[K] L) (S : Set (HeightOneSpectrum (𝓞 K))) :
    AddAut (↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S} → ℤ) :=
  permLatticeAut (galPermSL K L S σ)

@[scoped simp] theorem placePermAut_apply (σ : L ≃ₐ[K] L) (S : Set (HeightOneSpectrum (𝓞 K)))
    (f : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S} → ℤ) (w : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}) :
    placePermAut K L σ S f w = f ((galPermSL K L S σ).symm w) :=
  rfl

theorem placePermAut_apply_coe (σ : L ≃ₐ[K] L) (S : Set (HeightOneSpectrum (𝓞 K)))
    (f : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S} → ℤ) (w : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}) :
    placePermAut K L σ S f w = f ⟨σ⁻¹ • w.1, by
      show (σ⁻¹ • w.1).under (𝓞 K) ∈ S
      rw [place_under_smul]; exact w.2⟩ :=
  rfl

theorem placePermAut_pow_card (σ : L ≃ₐ[K] L) (S : Set (HeightOneSpectrum (𝓞 K))) :
    placePermAut K L σ S ^ Nat.card (L ≃ₐ[K] L) = 1 :=
  permLatticeAut_pow_eq_one (map_pow_natCard_eq_one (galPermSL K L S) σ)

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 K)) : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v := by
  haveI := v.isPrime
  obtain ⟨⟨Q, hQ⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 L)
  exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot hQ⟩, HeightOneSpectrum.ext hQ.2.over.symm⟩

theorem exists_smul_eq_of_under_eq {w w' : HeightOneSpectrum (𝓞 L)} (h : w.under (𝓞 K) = w'.under (𝓞 K)) :
    ∃ τ : L ≃ₐ[K] L, τ • w = w' := by
  haveI := w.isPrime
  haveI := w'.isPrime
  haveI : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  haveI : w'.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨by rw [h]; rfl⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 K)).asIdeal w.asIdeal w'.asIdeal (L ≃ₐ[K] L)
  exact ⟨τ, HeightOneSpectrum.ext hτ⟩

omit [IsGalois K L] in

theorem finite_placesOver (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))} := by
  have heq : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))}
      = finitePlacesOver (A := 𝓞 K) (B := 𝓞 L) ↑S :=
    Set.ext fun w => by
      show w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K))) ↔ underPlace (A := 𝓞 K) w ∈ (↑S : Set _)
      rw [show underPlace (A := 𝓞 K) w = w.under (𝓞 K) from HeightOneSpectrum.ext rfl]
  rw [heq]
  exact Finite.of_equiv _ (finitePlacesOverEquivSigma (A := 𝓞 K) (B := 𝓞 L) ↑S).symm

omit [NumberField K] [NumberField L] [IsGalois K L] in

def fibreEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) (v : ↥S) :
    {x : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))} //
        (⟨x.1.under (𝓞 K), x.2⟩ : ↥S) = v}
      ≃ {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  invFun w := ⟨⟨w.1, show w.1.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K))) by rw [w.2]; exact v.2⟩, Subtype.ext w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def placePermPair (σ : L ≃ₐ[K] L) (S : Set (HeightOneSpectrum (𝓞 K))) :
    HerbrandPair (↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S} → ℤ) :=
  HerbrandPair.ofAddAut (placePermAut K L σ S) (Nat.card (L ≃ₐ[K] L)) (placePermAut_pow_card K L σ S)

theorem placePermPair_eq (σ : L ≃ₐ[K] L) (S : Set (HeightOneSpectrum (𝓞 K))) :
    placePermPair K L σ S = permLatticePair (galPermSL K L S σ) (Nat.card (L ≃ₐ[K] L))
      (map_pow_natCard_eq_one (galPermSL K L S) σ) := rfl

theorem tateCard_placePermPair (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (placePermPair K L σ ↑S).tateCard₀ = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / finSplit K L v
      ∧ (placePermPair K L σ ↑S).tateCard₁ = 1 := by
  haveI := finite_placesOver K L S

  let f : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))} → ↥S :=
    fun w => ⟨w.1.under (𝓞 K), w.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := exists_under_eq K L v
    exact ⟨⟨w, show w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K))) by rw [hw]; exact hv⟩, Subtype.ext hw⟩
  have hinv : ∀ (τ : L ≃ₐ[K] L) (w), f (galPermSL K L ↑S τ w) = f w := fun τ w => Subtype.ext (place_under_smul K L τ w.1)
  have htrans : ∀ w w', f w = f w' → ∃ τ : L ≃ₐ[K] L, galPermSL K L ↑S τ w = w' := by
    intro w w' h
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_under_eq K L (congrArg Subtype.val h)
    exact ⟨τ, Subtype.ext hτ⟩
  have key := tateCard_permLatticePair_of_generator (galPermSL K L ↑S) σ hσ f hf hinv htrans
  refine ⟨key.1.trans ?_, key.2⟩
  rw [← Finset.prod_coe_sort S]
  exact Finset.prod_congr rfl fun v _ => by rw [finSplit_def, Nat.card_congr (fibreEquiv K L S v)]

theorem tateCard₀_placePermPair (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (placePermPair K L σ ↑S).tateCard₀ = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / finSplit K L v :=
  (tateCard_placePermPair K L σ hσ S).1

theorem tateCard₁_placePermPair (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (placePermPair K L σ ↑S).tateCard₁ = 1 :=
  (tateCard_placePermPair K L σ hσ S).2

end FinitePlaces
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice"

section InfinitePlaces

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def infPermAut (σ : L ≃ₐ[K] L) : AddAut (InfinitePlace L → ℤ) :=
  permLatticeAut (MulAction.toPermHom (L ≃ₐ[K] L) (InfinitePlace L) σ)

@[scoped simp] theorem infPermAut_apply (σ : L ≃ₐ[K] L) (f : InfinitePlace L → ℤ) (w : InfinitePlace L) :
    infPermAut K L σ f w = f (σ⁻¹ • w) :=
  rfl

theorem infPermAut_pow_card (σ : L ≃ₐ[K] L) : infPermAut K L σ ^ Nat.card (L ≃ₐ[K] L) = 1 :=
  permLatticeAut_pow_eq_one (map_pow_natCard_eq_one (MulAction.toPermHom (L ≃ₐ[K] L) (InfinitePlace L)) σ)

def infPermPair (σ : L ≃ₐ[K] L) : HerbrandPair (InfinitePlace L → ℤ) :=
  HerbrandPair.ofAddAut (infPermAut K L σ) (Nat.card (L ≃ₐ[K] L)) (infPermAut_pow_card K L σ)

theorem infPermPair_eq (σ : L ≃ₐ[K] L) :
    infPermPair K L σ = permLatticePair (MulAction.toPermHom (L ≃ₐ[K] L) (InfinitePlace L) σ) (Nat.card (L ≃ₐ[K] L))
      (map_pow_natCard_eq_one (MulAction.toPermHom (L ≃ₐ[K] L) (InfinitePlace L)) σ) := rfl

variable [NumberField K] [NumberField L] [IsGalois K L]

theorem tateCard_infPermPair (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (infPermPair K L σ).tateCard₀ = ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / infSplit K L v
      ∧ (infPermPair K L σ).tateCard₁ = 1 := by

  have hf : Function.Surjective fun w : InfinitePlace L => w.comap (algebraMap K L) := InfinitePlace.comap_surjective
  have hinv : ∀ (τ : L ≃ₐ[K] L) (w : InfinitePlace L),
      (MulAction.toPermHom (L ≃ₐ[K] L) (InfinitePlace L) τ w).comap (algebraMap K L) = w.comap (algebraMap K L) :=
    fun τ w => (InfinitePlace.mem_orbit_iff.1 (MulAction.mem_orbit w τ)).symm
  have htrans : ∀ w w' : InfinitePlace L, w.comap (algebraMap K L) = w'.comap (algebraMap K L) →
      ∃ τ : L ≃ₐ[K] L, MulAction.toPermHom (L ≃ₐ[K] L) (InfinitePlace L) τ w = w' :=
    fun w w' h => InfinitePlace.exists_smul_eq_of_comap_eq h
  exact tateCard_permLatticePair_of_generator (MulAction.toPermHom (L ≃ₐ[K] L) (InfinitePlace L)) σ hσ
    (fun w : InfinitePlace L => w.comap (algebraMap K L)) hf hinv htrans

theorem tateCard₀_infPermPair (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (infPermPair K L σ).tateCard₀ = ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / infSplit K L v :=
  (tateCard_infPermPair K L σ hσ).1

theorem tateCard₁_infPermPair (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (infPermPair K L σ).tateCard₁ = 1 :=
  (tateCard_infPermPair K L σ hσ).2

end InfinitePlaces
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice"

end M4aHerbrand.PlacePermLattice
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice"

end
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section Battery
#print axioms M4aHerbrand.PermLattice.permLatticeAut
#print axioms M4aHerbrand.PermLattice.permLatticeAut_pow_eq_one
#print axioms M4aHerbrand.PermLattice.permLatticePair
#print axioms M4aHerbrand.PermLattice.tateCard_permLatticePair_of_isCycleOn
#print axioms M4aHerbrand.PermLattice.tateCard_permLatticePair_fibration
#print axioms M4aHerbrand.PermLattice.isCycleOn_fibre_of_generator
#print axioms M4aHerbrand.PermLattice.tateCard_permLatticePair_of_generator
#print axioms M4aHerbrand.PermLattice.subtypePerm_pow_apply_coe
#print axioms M4aHerbrand.PermLattice.ofAddAut_exp_congr
#print axioms M4aHerbrand.PermLattice.twistedShiftAut_one_apply
#print axioms M4aHerbrand.PlacePermLattice.place_under_smul
#print axioms M4aHerbrand.PlacePermLattice.exists_under_eq
#print axioms M4aHerbrand.PlacePermLattice.exists_smul_eq_of_under_eq
#print axioms M4aHerbrand.PlacePermLattice.finite_placesOver
#print axioms M4aHerbrand.PlacePermLattice.fibreEquiv
#print axioms M4aHerbrand.PlacePermLattice.galPermSL
#print axioms M4aHerbrand.PlacePermLattice.placePermAut
#print axioms M4aHerbrand.PlacePermLattice.placePermAut_apply_coe
#print axioms M4aHerbrand.PlacePermLattice.placePermAut_pow_card
#print axioms M4aHerbrand.PlacePermLattice.placePermPair
#print axioms M4aHerbrand.PlacePermLattice.tateCard_placePermPair
#print axioms M4aHerbrand.PlacePermLattice.tateCard₀_placePermPair
#print axioms M4aHerbrand.PlacePermLattice.tateCard₁_placePermPair
#print axioms M4aHerbrand.PlacePermLattice.infPermAut
#print axioms M4aHerbrand.PlacePermLattice.infPermAut_pow_card
#print axioms M4aHerbrand.PlacePermLattice.infPermPair
#print axioms M4aHerbrand.PlacePermLattice.tateCard_infPermPair
#print axioms M4aHerbrand.PlacePermLattice.tateCard₀_infPermPair
#print axioms M4aHerbrand.PlacePermLattice.tateCard₁_infPermPair
end Battery
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section ed19Prints
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @M4aHerbrand.PermLattice.permLatticeAut
#check @M4aHerbrand.PermLattice.tateCard_permLatticePair_of_isCycleOn
#check @M4aHerbrand.PermLattice.tateCard_permLatticePair_fibration
#check @M4aHerbrand.PermLattice.tateCard_permLatticePair_of_generator
#check @M4aHerbrand.PlacePermLattice.galPermSL
#check @M4aHerbrand.PlacePermLattice.placePermAut
#check @M4aHerbrand.PlacePermLattice.placePermAut_apply_coe
#check @M4aHerbrand.PlacePermLattice.placePermPair
#check @M4aHerbrand.PlacePermLattice.tateCard₀_placePermPair
#check @M4aHerbrand.PlacePermLattice.tateCard₁_placePermPair
#check @M4aHerbrand.PlacePermLattice.infPermAut
#check @M4aHerbrand.PlacePermLattice.tateCard₀_infPermPair
#check @M4aHerbrand.PlacePermLattice.tateCard₁_infPermPair
end ed19Prints
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

end Fold_PlacePermLattice
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section Fold_RationalData

set_option autoImplicit false

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace RationalData
p2m_open "M4aHerbrand"

open TensorProduct M4aLocalCFT M4aLocalCFT.HerbrandPair

theorem flat_int_rat : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

attribute [local instance] flat_int_rat

section Denominators

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V] [Module ℚ V]

theorem exists_nsmul_mem_range_of_span_eq_top (ι : U →+ V)
    (hspan : Submodule.span ℚ (Set.range ι) = ⊤) (v : V) :
    ∃ m : ℕ, m ≠ 0 ∧ m • v ∈ ι.range := by
  have hv : v ∈ Submodule.span ℚ (Set.range ι) := by
    rw [hspan]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact ⟨u, rfl⟩⟩
  | zero =>
      exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨mx, hmx0, hmx⟩ := ihx
      obtain ⟨my, hmy0, hmy⟩ := ihy
      refine ⟨mx * my, Nat.mul_ne_zero hmx0 hmy0, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact nsmul_mem hmx my
      · rw [mul_smul]
        exact nsmul_mem hmy mx
  | smul q x hx ihx =>
      obtain ⟨mx, hmx0, hmx⟩ := ihx
      refine ⟨q.den * mx, Nat.mul_ne_zero q.den_ne_zero hmx0, ?_⟩
      have key : (q.den * mx : ℕ) • (q • x) = q.num • (mx • x) := by
        rw [← Nat.cast_smul_eq_nsmul ℚ (q.den * mx) (q • x),
          ← Int.cast_smul_eq_zsmul ℚ q.num (mx • x),
          ← Nat.cast_smul_eq_nsmul ℚ mx x, smul_smul, smul_smul]
        congr 1
        push_cast
        rw [← Rat.mul_den_eq_num q]
        ring
      rw [key]
      exact zsmul_mem hmx q.num

end Denominators
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section Hull

variable (A : Type*) [AddCommGroup A]

def hullAut : AddAut A →* AddAut (ℚ ⊗[ℤ] A) where
  toFun σ := (σ.toIntLinearEquiv.baseChange ℤ ℚ A A).toAddEquiv
  map_one' := by
    refine AddEquiv.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul q a => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_mul' σ τ := by
    refine AddEquiv.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul q a => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

@[scoped simp] theorem hullAut_tmul (σ : AddAut A) (q : ℚ) (a : A) : hullAut A σ (q ⊗ₜ[ℤ] a) = q ⊗ₜ[ℤ] σ a := rfl

theorem hullAut_pow_eq_one {σ : AddAut A} {n : ℕ} (hσ : σ ^ n = 1) : hullAut A σ ^ n = 1 := by
  rw [← map_pow, hσ, map_one]

theorem hullAut_smul (σ : AddAut A) (q : ℚ) (x : ℚ ⊗[ℤ] A) : hullAut A σ (q • x) = q • hullAut A σ x :=
  (σ.toIntLinearEquiv.baseChange ℤ ℚ A A).map_smul q x

def hullEmbed : A →+ ℚ ⊗[ℤ] A :=
  ((TensorProduct.mk ℤ ℚ A) 1).toAddMonoidHom

@[scoped simp] theorem hullEmbed_apply (a : A) : hullEmbed A a = (1 : ℚ) ⊗ₜ[ℤ] a := rfl

theorem hullAut_hullEmbed (σ : AddAut A) (a : A) : hullAut A σ (hullEmbed A a) = hullEmbed A (σ a) := rfl

theorem span_hullEmbed_range : Submodule.span ℚ (Set.range (hullEmbed A)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul q u =>
      have h : q ⊗ₜ[ℤ] u = q • ((1 : ℚ) ⊗ₜ[ℤ] u) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h]
      exact Submodule.smul_mem _ q (Submodule.subset_span ⟨u, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

theorem hullEmbed_injective [Module.Free ℤ A] : Function.Injective (hullEmbed A) := by
  have hfactor : ∀ u : A,
      hullEmbed A u = (Algebra.linearMap ℤ ℚ).rTensor A ((TensorProduct.lid ℤ A).symm u) := by
    intro u
    rw [hullEmbed_apply, TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul]
    norm_num
  have hcast : Function.Injective (Algebra.linearMap ℤ ℚ) := fun a b h => by
    have h' : (a : ℚ) = (b : ℚ) := h
    exact_mod_cast h'
  have hrinj : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor A) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hcast
  intro x y hxy
  rw [hfactor x, hfactor y] at hxy
  exact (TensorProduct.lid ℤ A).symm.injective (hrinj hxy)

theorem exists_nsmul_mem_hullEmbed_range (x : ℚ ⊗[ℤ] A) : ∃ m : ℕ, m ≠ 0 ∧ m • x ∈ (hullEmbed A).range :=
  exists_nsmul_mem_range_of_span_eq_top _ (span_hullEmbed_range A) x

def hullPair (σ : AddAut A) (n : ℕ) (hσ : σ ^ n = 1) : HerbrandPair (ℚ ⊗[ℤ] A) :=
  ofAddAut (hullAut A σ) n (hullAut_pow_eq_one A hσ)

theorem hullPair_def (σ : AddAut A) (n : ℕ) (hσ : σ ^ n = 1) :
    hullPair A σ n hσ = ofAddAut (hullAut A σ) n (hullAut_pow_eq_one A hσ) := rfl

theorem exists_finset_closure_eq_top [Module.Finite ℤ A] : ∃ s : Finset A, AddSubgroup.closure (s : Set A) = ⊤ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := A)
  refine ⟨s, ?_⟩
  rw [← Submodule.span_int_eq_addSubgroupClosure, hs]
  rfl

end Hull
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section Comp

variable (A B : Type*) [AddCommGroup A] [AddCommGroup B]

def compEmbed (φ : ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] B) : A →+ ℚ ⊗[ℤ] B :=
  φ.toLinearMap.toAddMonoidHom.comp (hullEmbed A)

@[scoped simp] theorem compEmbed_apply (φ : ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] B) (a : A) : compEmbed A B φ a = φ (hullEmbed A a) := rfl

theorem compEmbed_injective [Module.Free ℤ A] (φ : ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] B) :
    Function.Injective (compEmbed A B φ) :=
  φ.injective.comp (hullEmbed_injective A)

theorem span_compEmbed_range (φ : ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] B) :
    Submodule.span ℚ (Set.range (compEmbed A B φ)) = ⊤ := by
  have h : Set.range (compEmbed A B φ) = φ.toLinearMap '' Set.range (hullEmbed A) := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, span_hullEmbed_range, Submodule.map_top, LinearEquiv.range]

theorem exists_nsmul_mem_compEmbed_range (φ : ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] B) (x : ℚ ⊗[ℤ] B) :
    ∃ m : ℕ, m ≠ 0 ∧ m • x ∈ (compEmbed A B φ).range :=
  exists_nsmul_mem_range_of_span_eq_top _ (span_compEmbed_range A B φ) x

theorem compEmbed_equivariant (φ : ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] B) (α : AddAut A) (β : AddAut B)
    (hφ : ∀ x, φ (hullAut A α x) = hullAut B β (φ x)) (a : A) :
    compEmbed A B φ (α a) = hullAut B β (compEmbed A B φ a) := by
  rw [compEmbed_apply, compEmbed_apply, ← hullAut_hullEmbed, hφ]

end Comp
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section CrossEquation

universe u

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
  [Module.Finite ℤ A] [Module.Free ℤ A] [Module.Finite ℤ B] [Module.Free ℤ B]

theorem tateCard_cross_eq_of_linearEquiv (α : AddAut A) (β : AddAut B) {n : ℕ} (hα : α ^ n = 1) (hβ : β ^ n = 1)
    (φ : ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] B) (hφ : ∀ x, φ (hullAut A α x) = hullAut B β (φ x)) :
    (ofAddAut α n hα).tateCard₀ * (ofAddAut β n hβ).tateCard₁
      = (ofAddAut β n hβ).tateCard₀ * (ofAddAut α n hα).tateCard₁ := by
  obtain ⟨s, hs⟩ := exists_finset_closure_eq_top A
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top B
  have hfA : ∀ a, compEmbed A B φ (α a) = hullAut B β (compEmbed A B φ a) := compEmbed_equivariant A B φ α β hφ
  have hfB : ∀ b, hullEmbed B (β b) = hullAut B β (hullEmbed B b) := fun b => rfl
  exact tateCard_cross_eq_of_rational_equiv (ofAddAut α n hα) (ofAddAut β n hβ) (hullPair B β n hβ)
    (compEmbed A B φ) (hullEmbed B) (compEmbed_injective A B φ) (hullEmbed_injective B)
    (fun a => FirstInequalityShape.derive_comm α (hullAut B β) (compEmbed A B φ) hfA hα (hullAut_pow_eq_one B hβ) a)
    (fun a => FirstInequalityShape.norm_comm α (hullAut B β) (compEmbed A B φ) hfA hα (hullAut_pow_eq_one B hβ) a)
    (fun b => FirstInequalityShape.derive_comm β (hullAut B β) (hullEmbed B) hfB hβ (hullAut_pow_eq_one B hβ) b)
    (fun b => FirstInequalityShape.norm_comm β (hullAut B β) (hullEmbed B) hfB hβ (hullAut_pow_eq_one B hβ) b)
    s hs (fun x _ => exists_nsmul_mem_hullEmbed_range B (compEmbed A B φ x))
    t ht (fun y _ => exists_nsmul_mem_compEmbed_range A B φ (hullEmbed B y))

end CrossEquation
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section FixedRanks

variable (A : Type*) [AddCommGroup A]

def intLin : AddAut A →* Module.End ℤ A where
  toFun σ := σ.toAddMonoidHom.toIntLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

@[scoped simp] theorem intLin_apply (σ : AddAut A) (a : A) : intLin A σ a = σ a := rfl

def hullEnd : AddAut A →* Module.End ℚ (ℚ ⊗[ℤ] A) :=
  (Module.End.baseChangeHom ℤ ℚ A).toRingHom.toMonoidHom.comp (intLin A)

theorem hullEnd_eq_baseChange (σ : AddAut A) : hullEnd A σ = (intLin A σ).baseChange ℚ := rfl

@[scoped simp] theorem hullEnd_tmul (σ : AddAut A) (q : ℚ) (a : A) : hullEnd A σ (q ⊗ₜ[ℤ] a) = q ⊗ₜ[ℤ] σ a := by
  rw [hullEnd_eq_baseChange, LinearMap.baseChange_tmul, intLin_apply]

theorem hullEnd_apply (σ : AddAut A) (x : ℚ ⊗[ℤ] A) : hullEnd A σ x = hullAut A σ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul q a => rw [hullEnd_tmul, hullAut_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem hullEnd_pow_eq_one {σ : AddAut A} {n : ℕ} (hσ : σ ^ n = 1) : hullEnd A σ ^ n = 1 := by
  rw [← map_pow, hσ, map_one]

def fixedSubmodule (σ : AddAut A) : Submodule ℤ A :=
  LinearMap.ker (intLin A σ - 1)

theorem mem_fixedSubmodule_iff (σ : AddAut A) (a : A) : a ∈ fixedSubmodule A σ ↔ σ a = a := by
  show a ∈ LinearMap.ker (intLin A σ - 1) ↔ σ a = a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, intLin_apply]

theorem finrank_ker_hullEnd_sub_one [Module.Finite ℤ A] [Module.IsTorsionFree ℤ A] (σ : AddAut A) :
    Module.finrank ℚ (LinearMap.ker (hullEnd A σ - 1)) = Module.finrank ℤ (fixedSubmodule A σ) := by
  classical
  haveI : Module.Finite ℤ (fixedSubmodule A σ) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  haveI : Module.IsTorsionFree ℤ (fixedSubmodule A σ) :=
    Function.Injective.moduleIsTorsionFree (fixedSubmodule A σ).subtype
      (Submodule.injective_subtype _) (fun r m => map_smul (fixedSubmodule A σ).subtype r m)
  have hinj : Function.Injective ((fixedSubmodule A σ).subtype.baseChange ℚ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (fixedSubmodule A σ).subtype
      (Submodule.injective_subtype _)
  have hexact : Function.Exact ((fixedSubmodule A σ).subtype.lTensor ℚ)
      ((intLin A σ - 1).lTensor ℚ) :=
    Module.Flat.lTensor_exact ℚ (LinearMap.exact_subtype_ker_map (intLin A σ - 1))
  have hrange : LinearMap.ker (hullEnd A σ - 1)
      = LinearMap.range ((fixedSubmodule A σ).subtype.baseChange ℚ) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, LinearMap.mem_range]
    constructor
    · intro hx
      have hker : ((intLin A σ - 1).baseChange ℚ) x = 0 := by
        rw [LinearMap.baseChange_sub, LinearMap.baseChange_one, LinearMap.sub_apply,
          Module.End.one_apply, sub_eq_zero, ← hullEnd_eq_baseChange]
        exact hx
      exact (hexact x).mp hker
    · rintro ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul q k =>
          rw [LinearMap.baseChange_tmul, hullEnd_tmul]
          congr 1
          exact (mem_fixedSubmodule_iff A σ ↑k).mp k.2
      | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  rw [hrange, ← LinearEquiv.finrank_eq (LinearEquiv.ofInjective _ hinj),
    Module.finrank_baseChange]

end FixedRanks
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section CrossEquationOfRanks

universe u

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
  [Module.Finite ℤ A] [Module.IsTorsionFree ℤ A] [Module.Finite ℤ B] [Module.IsTorsionFree ℤ B]

theorem tateCard_cross_eq_of_fixedRanks (α : AddAut A) (β : AddAut B) {n : ℕ} (hn : 0 < n)
    (hα : α ^ n = 1) (hβ : β ^ n = 1)
    (h : ∀ e ∈ n.divisors,
      Module.finrank ℤ (fixedSubmodule A (α ^ e)) = Module.finrank ℤ (fixedSubmodule B (β ^ e))) :
    (ofAddAut α n hα).tateCard₀ * (ofAddAut β n hβ).tateCard₁
      = (ofAddAut β n hβ).tateCard₀ * (ofAddAut α n hα).tateCard₁ := by
  have h' : ∀ e ∈ n.divisors, Module.finrank ℚ (LinearMap.ker (hullEnd A α ^ e - 1))
      = Module.finrank ℚ (LinearMap.ker (hullEnd B β ^ e - 1)) := by
    intro e he
    rw [← map_pow, ← map_pow, finrank_ker_hullEnd_sub_one, finrank_ker_hullEnd_sub_one]
    exact h e he
  obtain ⟨φ, hφ⟩ := CyclicRational.exists_linearEquiv_intertwining_of_fixedRanks (hullEnd A α) (hullEnd B β) hn
    (hullEnd_pow_eq_one A hα) (hullEnd_pow_eq_one B hβ) h'
  exact tateCard_cross_eq_of_linearEquiv α β hα hβ φ fun x => by rw [← hullEnd_apply, ← hullEnd_apply]; exact hφ x

end CrossEquationOfRanks
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

section Products

variable (A B : Type*) [AddCommGroup A] [AddCommGroup B]

theorem prodCongr_pow (α : AddAut A) (β : AddAut B) (k : ℕ) : (α.prodCongr β) ^ k = (α ^ k).prodCongr (β ^ k) :=
  AddEquiv.ext fun z => by rw [HerbrandPi.prodCongr_pow_apply]; rfl

theorem mem_fixedSubmodule_prodCongr_iff (α : AddAut A) (β : AddAut B) (z : A × B) :
    z ∈ fixedSubmodule (A × B) (α.prodCongr β) ↔ z.1 ∈ fixedSubmodule A α ∧ z.2 ∈ fixedSubmodule B β := by
  rw [mem_fixedSubmodule_iff, mem_fixedSubmodule_iff, mem_fixedSubmodule_iff, Prod.ext_iff]
  rfl

def fixedSubmoduleProdEquiv (α : AddAut A) (β : AddAut B) :
    fixedSubmodule (A × B) (α.prodCongr β) ≃ₗ[ℤ] fixedSubmodule A α × fixedSubmodule B β where
  toFun z := (⟨z.1.1, ((mem_fixedSubmodule_prodCongr_iff A B α β z.1).1 z.2).1⟩,
    ⟨z.1.2, ((mem_fixedSubmodule_prodCongr_iff A B α β z.1).1 z.2).2⟩)
  invFun p := ⟨(p.1.1, p.2.1), (mem_fixedSubmodule_prodCongr_iff A B α β _).2 ⟨p.1.2, p.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_fixedSubmodule_prodCongr [Module.Finite ℤ A] [Module.IsTorsionFree ℤ A]
    [Module.Finite ℤ B] [Module.IsTorsionFree ℤ B] (α : AddAut A) (β : AddAut B) :
    Module.finrank ℤ (fixedSubmodule (A × B) (α.prodCongr β))
      = Module.finrank ℤ (fixedSubmodule A α) + Module.finrank ℤ (fixedSubmodule B β) := by
  haveI : Module.Finite ℤ (fixedSubmodule A α) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  haveI : Module.Finite ℤ (fixedSubmodule B β) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  haveI : Module.IsTorsionFree ℤ (fixedSubmodule A α) :=
    Function.Injective.moduleIsTorsionFree (fixedSubmodule A α).subtype
      (Submodule.injective_subtype _) (fun r m => map_smul (fixedSubmodule A α).subtype r m)
  haveI : Module.IsTorsionFree ℤ (fixedSubmodule B β) :=
    Function.Injective.moduleIsTorsionFree (fixedSubmodule B β).subtype
      (Submodule.injective_subtype _) (fun r m => map_smul (fixedSubmodule B β).subtype r m)
  rw [LinearEquiv.finrank_eq (fixedSubmoduleProdEquiv A B α β), Module.finrank_prod]

theorem fixedSubmodule_one : fixedSubmodule A (1 : AddAut A) = ⊤ := by
  show LinearMap.ker (intLin A 1 - 1) = ⊤
  rw [map_one, sub_self, LinearMap.ker_zero]

theorem finrank_fixedSubmodule_int_one_pow (e : ℕ) :
    Module.finrank ℤ (fixedSubmodule ℤ ((1 : AddAut ℤ) ^ e)) = 1 := by
  rw [one_pow, fixedSubmodule_one, finrank_top, Module.finrank_self]

end Products
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

end M4aHerbrand.RationalData
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice"

end
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section Battery
#print axioms M4aHerbrand.RationalData.exists_nsmul_mem_range_of_span_eq_top
#print axioms M4aHerbrand.RationalData.hullAut
#print axioms M4aHerbrand.RationalData.hullAut_pow_eq_one
#print axioms M4aHerbrand.RationalData.hullEmbed
#print axioms M4aHerbrand.RationalData.span_hullEmbed_range
#print axioms M4aHerbrand.RationalData.hullEmbed_injective
#print axioms M4aHerbrand.RationalData.hullPair
#print axioms M4aHerbrand.RationalData.exists_finset_closure_eq_top
#print axioms M4aHerbrand.RationalData.compEmbed
#print axioms M4aHerbrand.RationalData.compEmbed_injective
#print axioms M4aHerbrand.RationalData.span_compEmbed_range
#print axioms M4aHerbrand.RationalData.compEmbed_equivariant
#print axioms M4aHerbrand.RationalData.tateCard_cross_eq_of_linearEquiv
#print axioms M4aHerbrand.RationalData.intLin
#print axioms M4aHerbrand.RationalData.hullEnd
#print axioms M4aHerbrand.RationalData.hullEnd_apply
#print axioms M4aHerbrand.RationalData.hullEnd_pow_eq_one
#print axioms M4aHerbrand.RationalData.fixedSubmodule
#print axioms M4aHerbrand.RationalData.mem_fixedSubmodule_iff
#print axioms M4aHerbrand.RationalData.finrank_ker_hullEnd_sub_one
#print axioms M4aHerbrand.RationalData.tateCard_cross_eq_of_fixedRanks
#print axioms M4aHerbrand.RationalData.prodCongr_pow
#print axioms M4aHerbrand.RationalData.fixedSubmoduleProdEquiv
#print axioms M4aHerbrand.RationalData.finrank_fixedSubmodule_prodCongr
#print axioms M4aHerbrand.RationalData.fixedSubmodule_one
#print axioms M4aHerbrand.RationalData.finrank_fixedSubmodule_int_one_pow
end Battery
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section ed19Prints
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @M4aHerbrand.RationalData.hullAut
#check @M4aHerbrand.RationalData.hullEmbed
#check @M4aHerbrand.RationalData.tateCard_cross_eq_of_linearEquiv
#check @M4aHerbrand.RationalData.fixedSubmodule
#check @M4aHerbrand.RationalData.mem_fixedSubmodule_iff
#check @M4aHerbrand.RationalData.tateCard_cross_eq_of_fixedRanks
end ed19Prints
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end Fold_RationalData
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section Fold_SUnitBasic

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
p2m_open "M4aHerbrand"

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal WithZero

open scoped nonZeroDivisors

noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDedekindDomain R] in
theorem spanSingleton_units_ne_zero (x : Kˣ) : spanSingleton R⁰ (x : K) ≠ 0 :=
  spanSingleton_ne_zero_iff.mpr x.ne_zero

theorem count_spanSingleton_units_mul (v : HeightOneSpectrum R) (x y : Kˣ) :
    count K v (spanSingleton R⁰ ((x * y : Kˣ) : K)) =
      count K v (spanSingleton R⁰ (x : K)) + count K v (spanSingleton R⁰ (y : K)) := by
  rw [Units.val_mul, ← spanSingleton_mul_spanSingleton]
  exact count_mul K v (spanSingleton_units_ne_zero x) (spanSingleton_units_ne_zero y)

theorem count_spanSingleton_mk' (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) (s : R⁰) :
    count K v (spanSingleton R⁰ (IsLocalization.mk' K r s)) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ)
        - ((Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(s : R)} : Ideal R)).factors : ℤ) := by
  have hmk : IsLocalization.mk' K r s ≠ 0 := by
    rw [IsFractionRing.mk'_eq_div]
    exact div_ne_zero (by rwa [Ne, IsFractionRing.to_map_eq_zero_iff])
      (by rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact nonZeroDivisors.coe_ne_zero s)
  have hrep : spanSingleton R⁰ (IsLocalization.mk' K r s) =
      spanSingleton R⁰ ((algebraMap R K) (s : R))⁻¹ * ↑(Ideal.span {r} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, inv_mul_eq_div,
      ← IsFractionRing.mk'_eq_div]
  exact count_well_defined K v (spanSingleton_ne_zero_iff.mpr hmk) hrep

theorem valuation_eq_one_iff_count_eq_zero (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuation K (x : K) = 1 ↔ count K v (spanSingleton R⁰ (x : K)) = 0 := by
  obtain ⟨⟨r, s⟩, hx⟩ := IsLocalization.mk'_surjective (M := R⁰) (S := K) (x : K)
  change IsLocalization.mk' K r s = (x : K) at hx
  have hr : r ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hx
    exact x.ne_zero hx.symm
  rw [← hx, valuation_of_mk', count_spanSingleton_mk' v hr s,
    intValuation_if_neg v hr, intValuation_if_neg v (nonZeroDivisors.coe_ne_zero s),
    ← exp_sub, show (1 : ℤᵐ⁰) = exp 0 by rw [exp_zero], exp_inj]
  omega

theorem mem_unit_iff_count {T : Set (HeightOneSpectrum R)} {x : Kˣ} :
    x ∈ T.unit K ↔ ∀ v ∉ T, count K v (spanSingleton R⁰ (x : K)) = 0 := by
  have hmem : x ∈ T.unit K ↔
      ∀ v : HeightOneSpectrum R, v ∉ T → v.valuation K (x : K) = 1 := Iff.rfl
  rw [hmem]
  exact forall_congr' fun v => forall_congr' fun _ => valuation_eq_one_iff_count_eq_zero v x

def sUnitCountHom (T : Set (HeightOneSpectrum R)) :
    Additive ↥(T.unit K) →+ (↥T → ℤ) where
  toFun x v := count K (v : HeightOneSpectrum R)
    (spanSingleton R⁰ (((x.toMul : ↥(T.unit K)) : Kˣ) : K))
  map_zero' := by
    funext v
    show count K (v : HeightOneSpectrum R) (spanSingleton R⁰ ((1 : Kˣ) : K)) = 0
    rw [Units.val_one, spanSingleton_one, count_one]
  map_add' x y := by
    funext v
    show count K (v : HeightOneSpectrum R)
        (spanSingleton R⁰ (((x.toMul * y.toMul : ↥(T.unit K)) : Kˣ) : K)) = _
    have hco : ((x.toMul * y.toMul : ↥(T.unit K)) : Kˣ)
        = ((x.toMul : ↥(T.unit K)) : Kˣ) * ((y.toMul : ↥(T.unit K)) : Kˣ) := rfl
    rw [hco, count_spanSingleton_units_mul]
    rfl

@[scoped simp] theorem sUnitCountHom_apply (T : Set (HeightOneSpectrum R))
    (x : ↥(T.unit K)) (v : ↥T) :
    sUnitCountHom T (Additive.ofMul x) v
      = count K (v : HeightOneSpectrum R) (spanSingleton R⁰ ((x : Kˣ) : K)) :=
  rfl

theorem sUnitCountHom_apply' (T : Set (HeightOneSpectrum R))
    (x : Additive ↥(T.unit K)) (v : ↥T) :
    sUnitCountHom T x v
      = count K (v : HeightOneSpectrum R)
          (spanSingleton R⁰ (((x.toMul : ↥(T.unit K)) : Kˣ) : K)) :=
  rfl

theorem valuation_algebraMap_units_eq_one (v : HeightOneSpectrum R) (u : Rˣ) :
    v.valuation K (algebraMap R K (u : R)) = 1 := by
  have h1 : v.valuation K (algebraMap R K (u : R)) ≤ 1 := by
    rw [valuation_of_algebraMap]; exact v.intValuation_le_one _
  have h2 : v.valuation K (algebraMap R K ((u⁻¹ : Rˣ) : R)) ≤ 1 := by
    rw [valuation_of_algebraMap]; exact v.intValuation_le_one _
  have h3 : v.valuation K (algebraMap R K (u : R))
      * v.valuation K (algebraMap R K ((u⁻¹ : Rˣ) : R)) = 1 := by
    rw [← map_mul (v.valuation K), ← map_mul (algebraMap R K), Units.mul_inv, map_one, map_one]
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

def ringUnitsUnitHom (T : Set (HeightOneSpectrum R)) : Rˣ →* ↥(T.unit K) where
  toFun u := ⟨Units.map (algebraMap R K : R →* K) u, fun v _ => by
    show v.valuation K ((Units.map (algebraMap R K : R →* K) u : Kˣ) : K) = 1
    exact valuation_algebraMap_units_eq_one v u⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

@[scoped simp] theorem ringUnitsUnitHom_apply_coe (T : Set (HeightOneSpectrum R)) (u : Rˣ) :
    ((ringUnitsUnitHom (K := K) T u : ↥(T.unit K)) : Kˣ)
      = Units.map (algebraMap R K : R →* K) u :=
  rfl

theorem ringUnitsUnitHom_injective (T : Set (HeightOneSpectrum R)) :
    Function.Injective (ringUnitsUnitHom (K := K) (R := R) T) := fun _ _ h =>
  Units.map_injective (f := (algebraMap R K : R →* K))
    (IsFractionRing.injective R K) (Subtype.ext_iff.mp h)

theorem exists_ringUnits_eq_of_forall_valuation_eq_one {x : Kˣ}
    (h : ∀ v : HeightOneSpectrum R, v.valuation K (x : K) = 1) :
    ∃ u : Rˣ, Units.map (algebraMap R K : R →* K) u = x := by
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := R) K (x : K) fun v => (h v).le
  obtain ⟨s, hs⟩ := mem_integers_of_valuation_le_one (R := R) K ((x⁻¹ : Kˣ) : K) fun v =>
    le_of_eq (by rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one])
  have hrs : r * s = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_one, hr, hs, Units.val_inv_eq_inv_val, mul_inv_cancel₀ x.ne_zero]
  exact ⟨⟨r, s, hrs, by rwa [mul_comm] at hrs⟩, Units.ext hr⟩

noncomputable def ringUnitsAddEquivCountHomKer (T : Set (HeightOneSpectrum R)) :
    Additive Rˣ ≃+ ↥(sUnitCountHom (K := K) (R := R) T).ker := by
  refine AddEquiv.ofBijective
    (AddMonoidHom.codRestrict
      (MonoidHom.toAdditive (ringUnitsUnitHom (K := K) T)) _ ?_)
    ⟨?_, ?_⟩
  ·
    intro u
    show sUnitCountHom T (Additive.ofMul (ringUnitsUnitHom (K := K) T u.toMul)) = 0
    funext v
    rw [sUnitCountHom_apply, Pi.zero_apply]
    refine (valuation_eq_one_iff_count_eq_zero (v : HeightOneSpectrum R) _).mp ?_
    show (v : HeightOneSpectrum R).valuation K
        ((Units.map (algebraMap R K : R →* K) u.toMul : Kˣ) : K) = 1
    exact valuation_algebraMap_units_eq_one _ _
  ·
    intro a b h
    have h' := Subtype.ext_iff.mp h
    exact Additive.toMul.injective
      (ringUnitsUnitHom_injective (K := K) T (Additive.toMul.injective h'))
  ·
    rintro ⟨x, hx⟩
    set xm : ↥(T.unit K) := x.toMul with hxm
    have hall : ∀ v : HeightOneSpectrum R,
        count K v (spanSingleton R⁰ ((xm : Kˣ) : K)) = 0 := by
      intro v
      by_cases hvT : v ∈ T
      · have := congrFun hx ⟨v, hvT⟩
        rwa [sUnitCountHom_apply', Pi.zero_apply] at this
      · exact mem_unit_iff_count.mp xm.2 v hvT
    have hval : ∀ v : HeightOneSpectrum R, v.valuation K ((xm : Kˣ) : K) = 1 := fun v =>
      (valuation_eq_one_iff_count_eq_zero v _).mpr (hall v)
    obtain ⟨u, hu⟩ := exists_ringUnits_eq_of_forall_valuation_eq_one hval
    refine ⟨Additive.ofMul u, Subtype.ext ?_⟩
    show Additive.ofMul (ringUnitsUnitHom (K := K) T u) = x
    apply Additive.toMul.injective
    exact Subtype.ext hu

theorem moduleFinite_additive_unit (T : Set (HeightOneSpectrum R)) [Finite T]
    (hRu : Module.Finite ℤ (Additive Rˣ)) :
    Module.Finite ℤ (Additive ↥(T.unit K)) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (sUnitCountHom (K := K) (R := R) T).toIntLinearMap ?_ ?_
  · haveI : Fintype ↥T := Fintype.ofFinite ↥T
    have : Module.Finite ℤ (↥T → ℤ) := inferInstance
    exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv
      (ringUnitsAddEquivCountHomKer (K := K) (R := R) T).toIntLinearEquiv

end
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end M4aHerbrand
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section NumberFieldInstance

open NumberField

noncomputable scoped instance (K : Type*) [Field K] [NumberField K]
    (T : Set (IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K))) [Finite T] :
    Module.Finite ℤ (Additive ↥(T.unit K)) :=
  M4aHerbrand.moduleFinite_additive_unit T inferInstance

end NumberFieldInstance
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end Fold_SUnitBasic
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section Fold_TorsionCollapseCrossEquation

open Finset

namespace M4aLocalCFT

universe u

variable {A : Type u} [AddCommGroup A]

namespace HerbrandPair

noncomputable def restrictToSubgroup (P : HerbrandPair A) (S : AddSubgroup A)
    (hd : ∀ a ∈ S, P.derive a ∈ S) (hn : ∀ a ∈ S, P.norm a ∈ S) :
    HerbrandPair S where
  derive :=
    { toFun := fun a => ⟨P.derive a.1, hd a.1 a.2⟩
      map_zero' := Subtype.ext (map_zero P.derive)
      map_add' := fun a b => Subtype.ext (map_add P.derive a.1 b.1) }
  norm :=
    { toFun := fun a => ⟨P.norm a.1, hn a.1 a.2⟩
      map_zero' := Subtype.ext (map_zero P.norm)
      map_add' := fun a b => Subtype.ext (map_add P.norm a.1 b.1) }
  derive_norm a := Subtype.ext (P.derive_norm a.1)
  norm_derive a := Subtype.ext (P.norm_derive a.1)

@[scoped simp] theorem restrictToSubgroup_derive_coe (P : HerbrandPair A) (S : AddSubgroup A)
    (hd : ∀ a ∈ S, P.derive a ∈ S) (hn : ∀ a ∈ S, P.norm a ∈ S) (a : S) :
    (((P.restrictToSubgroup S hd hn).derive a : S) : A) = P.derive a :=
  rfl

@[scoped simp] theorem restrictToSubgroup_norm_coe (P : HerbrandPair A) (S : AddSubgroup A)
    (hd : ∀ a ∈ S, P.derive a ∈ S) (hn : ∀ a ∈ S, P.norm a ∈ S) (a : S) :
    (((P.restrictToSubgroup S hd hn).norm a : S) : A) = P.norm a :=
  rfl

theorem tateCard₀_of_subsingleton [Subsingleton A] (P : HerbrandPair A) :
    P.tateCard₀ = 1 := by
  haveI : Subsingleton (P.derive.ker ⧸ P.norm.range.addSubgroupOf P.derive.ker) := by
    refine ⟨fun x y => ?_⟩
    refine QuotientAddGroup.induction_on x fun a => ?_
    refine QuotientAddGroup.induction_on y fun b => ?_
    have hab : a = b := Subtype.ext (Subsingleton.elim _ _)
    rw [hab]
  haveI : Nonempty (P.derive.ker ⧸ P.norm.range.addSubgroupOf P.derive.ker) := ⟨0⟩
  rw [tateCard₀]
  exact Nat.card_unique

theorem tateCard₁_of_subsingleton [Subsingleton A] (P : HerbrandPair A) :
    P.tateCard₁ = 1 := by
  haveI : Subsingleton (P.norm.ker ⧸ P.derive.range.addSubgroupOf P.norm.ker) := by
    refine ⟨fun x y => ?_⟩
    refine QuotientAddGroup.induction_on x fun a => ?_
    refine QuotientAddGroup.induction_on y fun b => ?_
    have hab : a = b := Subtype.ext (Subsingleton.elim _ _)
    rw [hab]
  haveI : Nonempty (P.norm.ker ⧸ P.derive.range.addSubgroupOf P.norm.ker) := ⟨0⟩
  rw [tateCard₁]
  exact Nat.card_unique

theorem top_stable_derive (P : HerbrandPair A) :
    ∀ a ∈ (⊤ : AddSubgroup A), P.derive a ∈ (⊤ : AddSubgroup A) :=
  fun _ _ => AddSubgroup.mem_top _

theorem top_stable_norm (P : HerbrandPair A) :
    ∀ a ∈ (⊤ : AddSubgroup A), P.norm a ∈ (⊤ : AddSubgroup A) :=
  fun _ _ => AddSubgroup.mem_top _

end HerbrandPair
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

namespace HerbrandTriple

noncomputable def ofStableSubgroup (P : HerbrandPair A) (S : AddSubgroup A)
    (hd : ∀ a ∈ S, P.derive a ∈ S) (hn : ∀ a ∈ S, P.norm a ∈ S) :
    HerbrandTriple S A (A ⧸ S) where
  P := P.restrictToSubgroup S hd hn
  Q := P
  R := P.descendToQuotient S hd hn
  ι := S.subtype
  π := QuotientAddGroup.mk' S
  ι_injective := Subtype.coe_injective
  π_surjective := QuotientAddGroup.mk'_surjective S
  exact := (AddSubgroup.range_subtype S).trans (QuotientAddGroup.ker_mk' S).symm
  derive_ι _ := rfl
  norm_ι _ := rfl
  derive_π _ := rfl
  norm_π _ := rfl

theorem tateCard_mul_of_finite_sub {A B C : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (T : HerbrandTriple A B C) [Finite A] :
    T.Q.tateCard₀ * T.R.tateCard₁ = T.R.tateCard₀ * T.Q.tateCard₁ := by
  have key := T.tateCard_mul

  rw [T.P.tateCard₀_eq_tateCard₁_of_finite] at key
  have hP : T.P.tateCard₁ ≠ 0 := T.P.tateCard₁_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hP) ?_
  calc T.P.tateCard₁ * (T.Q.tateCard₀ * T.R.tateCard₁)
      = T.Q.tateCard₀ * T.P.tateCard₁ * T.R.tateCard₁ := by ring
    _ = T.P.tateCard₁ * T.R.tateCard₀ * T.Q.tateCard₁ := key.symm
    _ = T.P.tateCard₁ * (T.R.tateCard₀ * T.Q.tateCard₁) := by ring

end HerbrandTriple
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

theorem tateCard_cross_eq_of_finite_stable_subgroup (P : HerbrandPair A) (S : AddSubgroup A)
    [Finite S] (hd : ∀ a ∈ S, P.derive a ∈ S) (hn : ∀ a ∈ S, P.norm a ∈ S) :
    P.tateCard₀ * (P.descendToQuotient S hd hn).tateCard₁
      = (P.descendToQuotient S hd hn).tateCard₀ * P.tateCard₁ :=
  (HerbrandTriple.ofStableSubgroup P S hd hn).tateCard_mul_of_finite_sub

theorem tateCard_binder_transport_of_finite_stable_subgroup (P : HerbrandPair A)
    (S : AddSubgroup A) [Finite S]
    (hd : ∀ a ∈ S, P.derive a ∈ S) (hn : ∀ a ∈ S, P.norm a ∈ S) (p b : ℕ)
    (hQ : (P.descendToQuotient S hd hn).tateCard₀ * p
        = p ^ b * (P.descendToQuotient S hd hn).tateCard₁)
    (hQ₁ : (P.descendToQuotient S hd hn).tateCard₁ ≠ 0) :
    P.tateCard₀ * p = p ^ b * P.tateCard₁ := by
  have hcross := tateCard_cross_eq_of_finite_stable_subgroup P S hd hn
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hQ₁) ?_
  calc P.tateCard₀ * p * (P.descendToQuotient S hd hn).tateCard₁
      = (P.tateCard₀ * (P.descendToQuotient S hd hn).tateCard₁) * p := by ring
    _ = ((P.descendToQuotient S hd hn).tateCard₀ * P.tateCard₁) * p := by rw [hcross]
    _ = ((P.descendToQuotient S hd hn).tateCard₀ * p) * P.tateCard₁ := by ring
    _ = (p ^ b * (P.descendToQuotient S hd hn).tateCard₁) * P.tateCard₁ := by rw [hQ]
    _ = p ^ b * P.tateCard₁ * (P.descendToQuotient S hd hn).tateCard₁ := by ring

section Gates

open HerbrandPair

theorem prodGate_derive_apply (x : ℤ × ZMod 2) :
    (intTrivialPair.prod zmodTwoPair).derive x = 0 := by
  show (intTrivialPair.derive x.1, zmodTwoPair.derive x.2) = 0
  rw [intTrivialPair_derive_apply, zmodTwoPair_derive_apply]
  rfl

theorem prodGate_norm_apply (x : ℤ × ZMod 2) :
    (intTrivialPair.prod zmodTwoPair).norm x = (2 * x.1, 0) := by
  show (intTrivialPair.norm x.1, zmodTwoPair.norm x.2) = (2 * x.1, 0)
  rw [intTrivialPair_norm_apply, zmodTwoPair_norm_apply]

theorem gateStable_derive :
    ∀ x ∈ (AddMonoidHom.inr ℤ (ZMod 2)).range,
      (intTrivialPair.prod zmodTwoPair).derive x ∈ (AddMonoidHom.inr ℤ (ZMod 2)).range := by
  intro x _
  rw [prodGate_derive_apply]
  exact zero_mem _

theorem gateStable_norm :
    ∀ x ∈ (AddMonoidHom.inr ℤ (ZMod 2)).range,
      (intTrivialPair.prod zmodTwoPair).norm x ∈ (AddMonoidHom.inr ℤ (ZMod 2)).range := by
  rintro x ⟨c, rfl⟩
  rw [prodGate_norm_apply]
  have h1 : (AddMonoidHom.inr ℤ (ZMod 2) c).1 = 0 := rfl
  rw [h1, mul_zero]
  exact zero_mem _

theorem finite_inr_range : Finite ((AddMonoidHom.inr ℤ (ZMod 2)).range) :=
  Finite.of_surjective
    (fun c : ZMod 2 =>
      (⟨AddMonoidHom.inr ℤ (ZMod 2) c, ⟨c, rfl⟩⟩ : (AddMonoidHom.inr ℤ (ZMod 2)).range))
    (by rintro ⟨x, c, rfl⟩; exact ⟨c, rfl⟩)

noncomputable def gateDescendedPair :
    HerbrandPair ((ℤ × ZMod 2) ⧸ (AddMonoidHom.inr ℤ (ZMod 2)).range) :=
  (intTrivialPair.prod zmodTwoPair).descendToQuotient
    (AddMonoidHom.inr ℤ (ZMod 2)).range gateStable_derive gateStable_norm

theorem gateDescendedPair_derive_mk (x : ℤ × ZMod 2) :
    gateDescendedPair.derive (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk ((intTrivialPair.prod zmodTwoPair).derive x) :=
  rfl

theorem gateDescendedPair_norm_mk (x : ℤ × ZMod 2) :
    gateDescendedPair.norm (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk ((intTrivialPair.prod zmodTwoPair).norm x) :=
  rfl

theorem gate_torsion_collapse_fires :
    (intTrivialPair.prod zmodTwoPair).tateCard₀ * gateDescendedPair.tateCard₁
      = gateDescendedPair.tateCard₀ * (intTrivialPair.prod zmodTwoPair).tateCard₁ := by
  haveI := finite_inr_range
  exact tateCard_cross_eq_of_finite_stable_subgroup (intTrivialPair.prod zmodTwoPair) _
    gateStable_derive gateStable_norm

noncomputable def gateSection :
    ℤ →+ (ℤ × ZMod 2) ⧸ (AddMonoidHom.inr ℤ (ZMod 2)).range :=
  (QuotientAddGroup.mk' _).comp (AddMonoidHom.inl ℤ (ZMod 2))

theorem gateSection_apply (a : ℤ) :
    gateSection a = QuotientAddGroup.mk ((a : ℤ), (0 : ZMod 2)) :=
  rfl

theorem gateSection_bijective : Function.Bijective gateSection := by
  constructor
  · intro a b hab
    rw [gateSection_apply, gateSection_apply] at hab
    obtain ⟨c, hc⟩ := QuotientAddGroup.eq.mp hab
    have h1 : (0 : ℤ) = -a + b := congrArg Prod.fst hc
    omega
  · intro x
    refine QuotientAddGroup.induction_on x fun y => ?_
    refine ⟨y.1, ?_⟩
    rw [gateSection_apply, QuotientAddGroup.eq]
    refine ⟨y.2, ?_⟩
    show ((0 : ℤ), y.2) = (-y.1 + y.1, -(0 : ZMod 2) + y.2)
    rw [neg_add_cancel, neg_zero, zero_add]

theorem gateSection_intertwines_derive (a : ℤ) :
    gateDescendedPair.derive (gateSection a) = gateSection (intTrivialPair.derive a) := by
  rw [intTrivialPair_derive_apply, map_zero, gateSection_apply, gateDescendedPair_derive_mk,
    prodGate_derive_apply, QuotientAddGroup.mk_zero]

theorem gateSection_intertwines_norm (a : ℤ) :
    gateDescendedPair.norm (gateSection a) = gateSection (intTrivialPair.norm a) := by
  rw [intTrivialPair_norm_apply, gateSection_apply, gateDescendedPair_norm_mk,
    prodGate_norm_apply, gateSection_apply]

theorem gate_committed_route_cross :
    intTrivialPair.tateCard₀ * gateDescendedPair.tateCard₁
      = gateDescendedPair.tateCard₀ * intTrivialPair.tateCard₁ :=
  tateCard_cross_eq_of_addEquiv intTrivialPair gateDescendedPair
    (AddEquiv.ofBijective gateSection gateSection_bijective)
    (fun a => by
      simp only [AddEquiv.ofBijective_apply]
      exact gateSection_intertwines_derive a)
    (fun a => by
      simp only [AddEquiv.ofBijective_apply]
      exact gateSection_intertwines_norm a)

theorem gate_two_routes_agree :
    (intTrivialPair.prod zmodTwoPair).tateCard₀ * gateDescendedPair.tateCard₁
      = gateDescendedPair.tateCard₀ * (intTrivialPair.prod zmodTwoPair).tateCard₁ := by
  have h := gate_committed_route_cross
  rw [tateCard₁_intTrivialPair, mul_one] at h
  rw [HerbrandPair.tateCard₀_prod, HerbrandPair.tateCard₁_prod, tateCard₁_intTrivialPair,
    one_mul, ← zmodTwoPair.tateCard₀_eq_tateCard₁_of_finite, ← h]
  ring

theorem gate_finiteness_load_bearing :
    ¬ (intTrivialPair.tateCard₀
          * (intTrivialPair.descendToQuotient ⊤ intTrivialPair.top_stable_derive
              intTrivialPair.top_stable_norm).tateCard₁
        = (intTrivialPair.descendToQuotient ⊤ intTrivialPair.top_stable_derive
              intTrivialPair.top_stable_norm).tateCard₀
          * intTrivialPair.tateCard₁) := by
  haveI : Subsingleton (ℤ ⧸ (⊤ : AddSubgroup ℤ)) :=
    QuotientAddGroup.subsingleton_quotient_top
  have hQ₀ : (intTrivialPair.descendToQuotient ⊤ intTrivialPair.top_stable_derive
      intTrivialPair.top_stable_norm).tateCard₀ = 1 :=
    HerbrandPair.tateCard₀_of_subsingleton _
  have hQ₁ : (intTrivialPair.descendToQuotient ⊤ intTrivialPair.top_stable_derive
      intTrivialPair.top_stable_norm).tateCard₁ = 1 :=
    HerbrandPair.tateCard₁_of_subsingleton _
  rw [hQ₀, hQ₁, mul_one, one_mul]
  exact tateCard₀_ne_tateCard₁_int

def gateSwapAut : AddAut (ZMod 2 × ZMod 2) where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv := Prod.swap_swap
  right_inv := Prod.swap_swap
  map_add' _ _ := rfl

theorem gateSwapAut_sq : gateSwapAut ^ 2 = 1 := by
  rw [pow_two]
  ext x <;> rfl

theorem gate_stability_load_bearing :
    ¬ ∃ d : ((ZMod 2 × ZMod 2) ⧸ (AddMonoidHom.inr (ZMod 2) (ZMod 2)).range) →+
          ((ZMod 2 × ZMod 2) ⧸ (AddMonoidHom.inr (ZMod 2) (ZMod 2)).range),
        ∀ x : ZMod 2 × ZMod 2,
          d (QuotientAddGroup.mk x)
            = QuotientAddGroup.mk
                ((HerbrandPair.ofAddAut gateSwapAut 2 gateSwapAut_sq).derive x) := by
  rintro ⟨d, hd⟩

  have h01 : (QuotientAddGroup.mk ((0 : ZMod 2), (1 : ZMod 2)) :
      (ZMod 2 × ZMod 2) ⧸ (AddMonoidHom.inr (ZMod 2) (ZMod 2)).range)
        = QuotientAddGroup.mk ((0 : ZMod 2), (0 : ZMod 2)) := by
    rw [QuotientAddGroup.eq]
    refine ⟨1, ?_⟩
    show ((0 : ZMod 2), (1 : ZMod 2))
      = -((0 : ZMod 2), (1 : ZMod 2)) + ((0 : ZMod 2), (0 : ZMod 2))
    decide

  have key : (QuotientAddGroup.mk
        ((HerbrandPair.ofAddAut gateSwapAut 2 gateSwapAut_sq).derive
          ((0 : ZMod 2), (1 : ZMod 2))) :
      (ZMod 2 × ZMod 2) ⧸ (AddMonoidHom.inr (ZMod 2) (ZMod 2)).range)
        = QuotientAddGroup.mk
            ((HerbrandPair.ofAddAut gateSwapAut 2 gateSwapAut_sq).derive
              ((0 : ZMod 2), (0 : ZMod 2))) := by
    rw [← hd, ← hd, h01]
  rw [HerbrandPair.ofAddAut_derive_apply, HerbrandPair.ofAddAut_derive_apply] at key
  obtain ⟨c, hc⟩ := QuotientAddGroup.eq.mp key

  have hzero : (0 : ZMod 2)
      = -((gateSwapAut ((0 : ZMod 2), (1 : ZMod 2))).1 - 0)
        + ((gateSwapAut ((0 : ZMod 2), (0 : ZMod 2))).1 - 0) :=
    congrArg Prod.fst hc
  exact absurd hzero (by decide)

theorem gate_binder_transport_fires :
    zmodTwoPair.tateCard₀ * 2 = 2 ^ 1 * zmodTwoPair.tateCard₁ := by
  haveI : Subsingleton (ZMod 2 ⧸ (⊤ : AddSubgroup (ZMod 2))) :=
    QuotientAddGroup.subsingleton_quotient_top
  refine tateCard_binder_transport_of_finite_stable_subgroup zmodTwoPair ⊤
    zmodTwoPair.top_stable_derive zmodTwoPair.top_stable_norm 2 1 ?_ ?_
  · rw [HerbrandPair.tateCard₀_of_subsingleton, HerbrandPair.tateCard₁_of_subsingleton]
    norm_num
  · rw [HerbrandPair.tateCard₁_of_subsingleton]
    exact one_ne_zero

theorem gate_binder_transport_disjoint_route :
    zmodTwoPair.tateCard₀ * 2 = 2 ^ 1 * zmodTwoPair.tateCard₁ := by
  rw [zmodTwoPair.tateCard₀_eq_tateCard₁_of_finite]
  ring

end Gates
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end Fold_TorsionCollapseCrossEquation
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section Fold_UnitLatticeAssembly

set_option autoImplicit false

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace UnitLatticeAssembly
p2m_open "M4aHerbrand"

open M4aLocalCFT M4aLocalCFT.HerbrandPair M4aLocalCFT.LocalUnitsCohomology

universe u uK uL

section Generic

variable {U W V : Type u} [AddCommGroup U] [AddCommGroup W] [AddCommGroup V] [Module ℚ V]

theorem tateCard_mul_of_rational_data (P : HerbrandPair U) (Q : HerbrandPair W) (R : HerbrandPair V)
    {n N : ℕ} (hn : n ≠ 0) (hQ₀ : Q.tateCard₀ = N) (hQ₁ : Q.tateCard₁ = 1)
    (ιA : U × ℤ →+ V) (ιB : W →+ V)
    (hιA : Function.Injective ιA) (hιB : Function.Injective ιB)
    (hdA : ∀ x, R.derive (ιA x) = ιA ((P.prod (intCyclicPair n)).derive x))
    (hnA : ∀ x, R.norm (ιA x) = ιA ((P.prod (intCyclicPair n)).norm x))
    (hdB : ∀ y, R.derive (ιB y) = ιB (Q.derive y))
    (hnB : ∀ y, R.norm (ιB y) = ιB (Q.norm y))
    (s : Finset (U × ℤ)) (hs : AddSubgroup.closure (s : Set (U × ℤ)) = ⊤)
    (hden : ∀ x ∈ s, ∃ m : ℕ, m ≠ 0 ∧ m • ιA x ∈ ιB.range)
    (t : Finset W) (ht : AddSubgroup.closure (t : Set W) = ⊤)
    (hden' : ∀ y ∈ t, ∃ m : ℕ, m ≠ 0 ∧ m • ιB y ∈ ιA.range) :
    P.tateCard₀ * n = N * P.tateCard₁ := by
  have key := tateCard_cross_eq_of_rational_equiv (P.prod (intCyclicPair n)) Q R ιA ιB hιA hιB hdA hnA hdB hnB
    s hs hden t ht hden'
  rw [tateCard₀_prod, tateCard₁_prod, tateCard₀_intCyclicPair hn, tateCard₁_intCyclicPair hn, hQ₀, hQ₁,
    mul_one, mul_one] at key
  exact key

end Generic
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section NumberField

open NumberField IsDedekindDomain M4aHerbrand.PlacePermLattice M4aHerbrand.LocalDegree

variable (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem tateCard₀_placePermPair_prod_infPermPair (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ((placePermPair K L σ ↑S).prod (infPermPair K L σ)).tateCard₀ = localDegreeProd K L S := by
  rw [tateCard₀_prod, tateCard₀_placePermPair K L σ hσ S, tateCard₀_infPermPair K L σ hσ, localDegreeProd_def]

theorem tateCard₁_placePermPair_prod_infPermPair (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ((placePermPair K L σ ↑S).prod (infPermPair K L σ)).tateCard₁ = 1 := by
  rw [tateCard₁_prod, tateCard₁_placePermPair K L σ hσ S, tateCard₁_infPermPair K L σ hσ, mul_one]

theorem hU_of_rational_data (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {U V : Type uL} [AddCommGroup U] [AddCommGroup V] [Module ℚ V] (P : HerbrandPair U) (R : HerbrandPair V)
    (ιA : U × ℤ →+ V)
    (ιB : (↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))} → ℤ)
      × (InfinitePlace L → ℤ) →+ V)
    (hιA : Function.Injective ιA) (hιB : Function.Injective ιB)
    (hdA : ∀ x, R.derive (ιA x) = ιA ((P.prod (intCyclicPair (Nat.card (L ≃ₐ[K] L)))).derive x))
    (hnA : ∀ x, R.norm (ιA x) = ιA ((P.prod (intCyclicPair (Nat.card (L ≃ₐ[K] L)))).norm x))
    (hdB : ∀ y, R.derive (ιB y) = ιB (((placePermPair K L σ ↑S).prod (infPermPair K L σ)).derive y))
    (hnB : ∀ y, R.norm (ιB y) = ιB (((placePermPair K L σ ↑S).prod (infPermPair K L σ)).norm y))
    (s : Finset (U × ℤ)) (hs : AddSubgroup.closure (s : Set (U × ℤ)) = ⊤)
    (hden : ∀ x ∈ s, ∃ m : ℕ, m ≠ 0 ∧ m • ιA x ∈ ιB.range)
    (t : Finset ((↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))} → ℤ)
      × (InfinitePlace L → ℤ)))
    (ht : AddSubgroup.closure (t : Set ((↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))}
      → ℤ) × (InfinitePlace L → ℤ))) = ⊤)
    (hden' : ∀ y ∈ t, ∃ m : ℕ, m ≠ 0 ∧ m • ιB y ∈ ιA.range) :
    P.tateCard₀ * Nat.card (L ≃ₐ[K] L) = localDegreeProd K L S * P.tateCard₁ :=
  tateCard_mul_of_rational_data P ((placePermPair K L σ ↑S).prod (infPermPair K L σ)) R Nat.card_pos.ne'
    (tateCard₀_placePermPair_prod_infPermPair K L σ hσ S) (tateCard₁_placePermPair_prod_infPermPair K L σ hσ S)
    ιA ιB hιA hιB hdA hnA hdB hnB s hs hden t ht hden'

theorem hU_of_fixedRanks (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {U : Type uL} [AddCommGroup U] [Module.Finite ℤ U] [Module.IsTorsionFree ℤ U]
    (σU : AddAut U) (hσU : σU ^ Nat.card (L ≃ₐ[K] L) = 1)
    (hrank : ∀ e ∈ (Nat.card (L ≃ₐ[K] L)).divisors,
      Module.finrank ℤ (RationalData.fixedSubmodule U (σU ^ e)) + 1
        = Module.finrank ℤ (RationalData.fixedSubmodule
            (↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))} → ℤ)
            (placePermAut K L σ ↑S ^ e))
          + Module.finrank ℤ (RationalData.fixedSubmodule (InfinitePlace L → ℤ) (infPermAut K L σ ^ e))) :
    (ofAddAut σU (Nat.card (L ≃ₐ[K] L)) hσU).tateCard₀ * Nat.card (L ≃ₐ[K] L)
      = localDegreeProd K L S * (ofAddAut σU (Nat.card (L ≃ₐ[K] L)) hσU).tateCard₁ := by
  have hn : 0 < Nat.card (L ≃ₐ[K] L) := Nat.card_pos
  haveI := finite_placesOver K L S
  have hα : σU.prodCongr (1 : AddAut ℤ) ^ Nat.card (L ≃ₐ[K] L) = 1 :=
    HerbrandPi.prodCongr_pow_eq_one σU 1 hσU (one_pow _)
  have hβ : (placePermAut K L σ ↑S).prodCongr (infPermAut K L σ) ^ Nat.card (L ≃ₐ[K] L) = 1 :=
    HerbrandPi.prodCongr_pow_eq_one (placePermAut K L σ ↑S) (infPermAut K L σ) (placePermAut_pow_card K L σ ↑S)
      (infPermAut_pow_card K L σ)
  have key := RationalData.tateCard_cross_eq_of_fixedRanks (σU.prodCongr (1 : AddAut ℤ))
    ((placePermAut K L σ ↑S).prodCongr (infPermAut K L σ)) hn hα hβ (fun e he => by
      rw [RationalData.prodCongr_pow, RationalData.prodCongr_pow, RationalData.finrank_fixedSubmodule_prodCongr,
        RationalData.finrank_fixedSubmodule_prodCongr, RationalData.finrank_fixedSubmodule_int_one_pow]
      exact hrank e he)
  rw [HerbrandPi.tateCard₀_ofAddAut_prodCongr σU 1 _ hσU (one_pow _) hα,
    HerbrandPi.tateCard₁_ofAddAut_prodCongr σU 1 _ hσU (one_pow _) hα,
    HerbrandPi.tateCard₀_ofAddAut_prodCongr (placePermAut K L σ ↑S) (infPermAut K L σ) _
      (placePermAut_pow_card K L σ ↑S) (infPermAut_pow_card K L σ) hβ,
    HerbrandPi.tateCard₁_ofAddAut_prodCongr (placePermAut K L σ ↑S) (infPermAut K L σ) _
      (placePermAut_pow_card K L σ ↑S) (infPermAut_pow_card K L σ) hβ,
    show ofAddAut (placePermAut K L σ ↑S) (Nat.card (L ≃ₐ[K] L)) (placePermAut_pow_card K L σ ↑S)
      = placePermPair K L σ ↑S from rfl,
    show ofAddAut (infPermAut K L σ) (Nat.card (L ≃ₐ[K] L)) (infPermAut_pow_card K L σ) = infPermPair K L σ from rfl,
    show ofAddAut (1 : AddAut ℤ) (Nat.card (L ≃ₐ[K] L)) (one_pow _) = intCyclicPair (Nat.card (L ≃ₐ[K] L)) from rfl,
    tateCard₀_placePermPair_prod_infPermPair K L σ hσ S, tateCard₁_placePermPair_prod_infPermPair K L σ hσ S,
    tateCard₀_prod, tateCard₁_prod, tateCard₀_intCyclicPair hn.ne', tateCard₁_intCyclicPair hn.ne',
    mul_one, mul_one] at key
  exact key

end NumberField
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end M4aHerbrand.UnitLatticeAssembly
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section Battery
#print axioms M4aHerbrand.UnitLatticeAssembly.tateCard_mul_of_rational_data
#print axioms M4aHerbrand.UnitLatticeAssembly.tateCard₀_placePermPair_prod_infPermPair
#print axioms M4aHerbrand.UnitLatticeAssembly.tateCard₁_placePermPair_prod_infPermPair
#print axioms M4aHerbrand.UnitLatticeAssembly.hU_of_rational_data
#print axioms M4aHerbrand.UnitLatticeAssembly.hU_of_fixedRanks
end Battery
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section ed19Prints
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @M4aHerbrand.UnitLatticeAssembly.tateCard_mul_of_rational_data
#check @M4aHerbrand.UnitLatticeAssembly.hU_of_rational_data
#check @M4aHerbrand.UnitLatticeAssembly.hU_of_fixedRanks
end ed19Prints
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end Fold_UnitLatticeAssembly
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

set_option autoImplicit false

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "sUnitQuot_fixedRank_eq"
namespace UherbSol
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain
open M4aLocalCFT M4aLocalCFT.HerbrandPair M4aLocalCFT.LocalUnitsCohomology
p2m_open "M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FirstInequalityShape P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle"
open M4aHerbrand.PlacePermLattice M4aHerbrand.LocalDegree

section GenericTorsion

variable {A : Type*} [AddCommGroup A]

theorem isOfFinAddOrder_addAut (α : AddAut A) {a : A} (ha : IsOfFinAddOrder a) : IsOfFinAddOrder (α a) := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at ha ⊢
  obtain ⟨m, hm, hma⟩ := ha
  exact ⟨m, hm, by rw [← map_nsmul, hma, map_zero]⟩

theorem addAut_mem_torsion (α : AddAut A) :
    ∀ a ∈ AddCommGroup.torsion A, α a ∈ AddCommGroup.torsion A :=
  fun _ ha => isOfFinAddOrder_addAut α ha

def addAutQuotTorsion (α : AddAut A) : AddAut (A ⧸ AddCommGroup.torsion A) :=
  quotAut α (AddCommGroup.torsion A) (addAut_mem_torsion α) (addAut_mem_torsion α.symm)

theorem addAutQuotTorsion_mk (α : AddAut A) (a : A) :
    addAutQuotTorsion α (QuotientAddGroup.mk a) = QuotientAddGroup.mk (α a) := rfl

theorem addAutQuotTorsion_pow_eq_one (α : AddAut A) {n : ℕ} (hα : α ^ n = 1) :
    addAutQuotTorsion α ^ n = 1 :=
  quotAut_pow_eq_one α (AddCommGroup.torsion A) _ _ hα

def ofAddAutQuotTorsion (α : AddAut A) {n : ℕ} (hα : α ^ n = 1) :
    HerbrandPair (A ⧸ AddCommGroup.torsion A) :=
  ofAddAut (addAutQuotTorsion α) n (addAutQuotTorsion_pow_eq_one α hα)

theorem torsion_stable_derive (α : AddAut A) {n : ℕ} (hα : α ^ n = 1) :
    ∀ a ∈ AddCommGroup.torsion A, (ofAddAut α n hα).derive a ∈ AddCommGroup.torsion A := by
  intro a ha
  rw [ofAddAut_derive_apply]
  exact sub_mem (isOfFinAddOrder_addAut α ha) ha

theorem torsion_stable_norm (α : AddAut A) {n : ℕ} (hα : α ^ n = 1) :
    ∀ a ∈ AddCommGroup.torsion A, (ofAddAut α n hα).norm a ∈ AddCommGroup.torsion A := by
  intro a ha
  rw [ofAddAut_norm_apply]
  exact sum_mem fun i _ => isOfFinAddOrder_addAut (α ^ i) ha

theorem tateCard₀_ofAddAutQuotTorsion_eq (α : AddAut A) {n : ℕ} (hα : α ^ n = 1) :
    (ofAddAutQuotTorsion α hα).tateCard₀
      = ((ofAddAut α n hα).descendToQuotient (AddCommGroup.torsion A)
          (torsion_stable_derive α hα) (torsion_stable_norm α hα)).tateCard₀ := by
  refine tateCard₀_congr _ _ (AddEquiv.refl _) ?_ ?_
  · intro x
    refine QuotientAddGroup.induction_on x fun a => ?_
    show ((ofAddAut α n hα).descendToQuotient _ _ _).derive (QuotientAddGroup.mk a)
      = (ofAddAutQuotTorsion α hα).derive (QuotientAddGroup.mk a)
    rw [descendToQuotient_derive_mk, ofAddAut_derive_apply]
    show QuotientAddGroup.mk (α a - a)
      = addAutQuotTorsion α (QuotientAddGroup.mk a) - QuotientAddGroup.mk a
    rw [addAutQuotTorsion_mk, ← QuotientAddGroup.mk_sub]
  · intro x
    refine QuotientAddGroup.induction_on x fun a => ?_
    show ((ofAddAut α n hα).descendToQuotient _ _ _).norm (QuotientAddGroup.mk a)
      = (ofAddAutQuotTorsion α hα).norm (QuotientAddGroup.mk a)
    rw [descendToQuotient_norm_mk, ofAddAut_norm_apply, ofAddAutQuotTorsion, ofAddAut_norm_apply]
    rw [show (QuotientAddGroup.mk (∑ i ∈ Finset.range n, (α ^ i) a) : A ⧸ AddCommGroup.torsion A)
      = ∑ i ∈ Finset.range n, QuotientAddGroup.mk ((α ^ i) a) from map_sum (QuotientAddGroup.mk' _) _ _]
    exact Finset.sum_congr rfl fun i _ =>
      (quotAut_pow_mk α (AddCommGroup.torsion A) _ _ i a).symm

theorem tateCard₁_ofAddAutQuotTorsion_eq (α : AddAut A) {n : ℕ} (hα : α ^ n = 1) :
    (ofAddAutQuotTorsion α hα).tateCard₁
      = ((ofAddAut α n hα).descendToQuotient (AddCommGroup.torsion A)
          (torsion_stable_derive α hα) (torsion_stable_norm α hα)).tateCard₁ := by
  refine tateCard₁_congr _ _ (AddEquiv.refl _) ?_ ?_
  · intro x
    refine QuotientAddGroup.induction_on x fun a => ?_
    show ((ofAddAut α n hα).descendToQuotient _ _ _).derive (QuotientAddGroup.mk a)
      = (ofAddAutQuotTorsion α hα).derive (QuotientAddGroup.mk a)
    rw [descendToQuotient_derive_mk, ofAddAut_derive_apply]
    show QuotientAddGroup.mk (α a - a)
      = addAutQuotTorsion α (QuotientAddGroup.mk a) - QuotientAddGroup.mk a
    rw [addAutQuotTorsion_mk, ← QuotientAddGroup.mk_sub]
  · intro x
    refine QuotientAddGroup.induction_on x fun a => ?_
    show ((ofAddAut α n hα).descendToQuotient _ _ _).norm (QuotientAddGroup.mk a)
      = (ofAddAutQuotTorsion α hα).norm (QuotientAddGroup.mk a)
    rw [descendToQuotient_norm_mk, ofAddAut_norm_apply, ofAddAutQuotTorsion, ofAddAut_norm_apply]
    rw [show (QuotientAddGroup.mk (∑ i ∈ Finset.range n, (α ^ i) a) : A ⧸ AddCommGroup.torsion A)
      = ∑ i ∈ Finset.range n, QuotientAddGroup.mk ((α ^ i) a) from map_sum (QuotientAddGroup.mk' _) _ _]
    exact Finset.sum_congr rfl fun i _ =>
      (quotAut_pow_mk α (AddCommGroup.torsion A) _ _ i a).symm

end GenericTorsion
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section GenericTransport

theorem tateCard_eq_transport_of_finite_stable_subgroup {A : Type*} [AddCommGroup A]
    (P : HerbrandPair A) (T : AddSubgroup A) [Finite T]
    (hd : ∀ a ∈ T, P.derive a ∈ T) (hn : ∀ a ∈ T, P.norm a ∈ T) (m N : ℕ)
    (hQ : (P.descendToQuotient T hd hn).tateCard₀ * m = N * (P.descendToQuotient T hd hn).tateCard₁)
    (hQ₁ : (P.descendToQuotient T hd hn).tateCard₁ ≠ 0) :
    P.tateCard₀ * m = N * P.tateCard₁ := by
  have hcross := tateCard_cross_eq_of_finite_stable_subgroup P T hd hn
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hQ₁) ?_
  calc P.tateCard₀ * m * (P.descendToQuotient T hd hn).tateCard₁
      = (P.tateCard₀ * (P.descendToQuotient T hd hn).tateCard₁) * m := by ring
    _ = ((P.descendToQuotient T hd hn).tateCard₀ * P.tateCard₁) * m := by rw [hcross]
    _ = ((P.descendToQuotient T hd hn).tateCard₀ * m) * P.tateCard₁ := by ring
    _ = (N * (P.descendToQuotient T hd hn).tateCard₁) * P.tateCard₁ := by rw [hQ]
    _ = N * P.tateCard₁ * (P.descendToQuotient T hd hn).tateCard₁ := by ring

theorem toAdditive_mulAut_pow {M : Type*} [Group M] (γ : M ≃* M) (e : ℕ) :
    (MulEquiv.toAdditive γ) ^ e = MulEquiv.toAdditive (γ ^ e) := by
  induction e with
  | zero =>
      apply AddEquiv.ext
      intro x
      rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      apply AddEquiv.ext
      intro x
      rfl

theorem torsion_mem_iff {A : Type*} [AddCommGroup A] (x : A) :
    x ∈ AddCommGroup.torsion A ↔ ∃ n : ℕ, n ≠ 0 ∧ n • x = 0 := by
  rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero]
  constructor
  · rintro ⟨n, hn, h⟩; exact ⟨n, Nat.pos_iff_ne_zero.mp hn, h⟩
  · rintro ⟨n, hn, h⟩; exact ⟨n, Nat.pos_iff_ne_zero.mpr hn, h⟩

end GenericTransport
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section WUnits

variable (L : Type*) [Field L] [NumberField L] (W : Set (HeightOneSpectrum (𝓞 L)))

theorem exists_ringUnits_eq_of_mem_torsion
    {l : Additive ↥(W.unit L)} (hl : l ∈ AddCommGroup.torsion (Additive ↥(W.unit L))) :
    ∃ u : (𝓞 L)ˣ, Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) u
      = ((Additive.toMul l : ↥(W.unit L)) : Lˣ) := by
  refine exists_ringUnits_eq_of_forall_valuation_eq_one (R := 𝓞 L) fun v => ?_
  have hlL : IsOfFinOrder ((Additive.toMul l : ↥(W.unit L)) : Lˣ) :=
    (Subgroup.subtype (W.unit L)).isOfFinOrder hl
  obtain ⟨m, hm, hlm⟩ := isOfFinOrder_iff_pow_eq_one.mp hlL
  have hvm : v.valuation L ((Additive.toMul l : ↥(W.unit L)) : Lˣ).val ^ m = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hlm, Units.val_one, map_one]
  rcases lt_trichotomy (v.valuation L ((Additive.toMul l : ↥(W.unit L)) : Lˣ).val) 1 with h | h | h
  · exact absurd hvm (ne_of_lt (pow_lt_one₀ (zero_le' (α := WithZero (Multiplicative ℤ))) h hm.ne'))
  · exact h
  · exact absurd hvm (ne_of_gt (one_lt_pow₀ h hm.ne'))

theorem torsion_injects_into_units_torsion :
    ∃ f : ↥(AddCommGroup.torsion (Additive ↥(W.unit L))) → NumberField.Units.torsion L,
      Function.Injective f := by
  classical
  have hinj := Units.map_injective
    (f := (algebraMap (𝓞 L) L : 𝓞 L →* L)) (IsFractionRing.injective (𝓞 L) L)
  refine ⟨fun x => ⟨(exists_ringUnits_eq_of_mem_torsion L W x.2).choose, ?_⟩, ?_⟩
  ·
    show IsOfFinOrder _
    have hspec := (exists_ringUnits_eq_of_mem_torsion L W x.2).choose_spec
    have hlL : IsOfFinOrder (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L)
        (exists_ringUnits_eq_of_mem_torsion L W x.2).choose) := by
      rw [hspec]
      exact (Subgroup.subtype (W.unit L)).isOfFinOrder x.2
    obtain ⟨m, hm, hlm⟩ := isOfFinOrder_iff_pow_eq_one.mp hlL
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hinj (by rw [map_pow, hlm, map_one])⟩
  ·
    intro x y hxy
    have hx := (exists_ringUnits_eq_of_mem_torsion L W x.2).choose_spec
    have hy := (exists_ringUnits_eq_of_mem_torsion L W y.2).choose_spec
    refine Subtype.ext (Additive.toMul.injective (Subtype.ext (a2 := Additive.toMul y.1) ?_))
    rw [← hx, ← hy]
    exact congrArg (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L)) (Subtype.ext_iff.mp hxy)

scoped instance instFiniteTorsion :
    Finite ↥(AddCommGroup.torsion (Additive ↥(W.unit L))) := by
  obtain ⟨f, hf⟩ := torsion_injects_into_units_torsion L W
  exact Finite.of_injective f hf

variable [Finite ↥W]

scoped instance instAddGroupFG : AddGroup.FG (Additive ↥(W.unit L)) :=
  Module.Finite.iff_addGroup_fg.mp (inferInstance : Module.Finite ℤ (Additive ↥(W.unit L)))

scoped instance instAddGroupFGQuotTorsion :
    AddGroup.FG (Additive ↥(W.unit L) ⧸ AddCommGroup.torsion (Additive ↥(W.unit L))) :=
  QuotientAddGroup.fg _

scoped instance instModuleFiniteQuotTorsion :
    Module.Finite ℤ (Additive ↥(W.unit L) ⧸ AddCommGroup.torsion (Additive ↥(W.unit L))) :=
  Module.Finite.iff_addGroup_fg.mpr (instAddGroupFGQuotTorsion L W)

scoped instance instIsTorsionFreeQuotTorsion :
    Module.IsTorsionFree ℤ (Additive ↥(W.unit L) ⧸ AddCommGroup.torsion (Additive ↥(W.unit L))) :=
  inferInstance

end WUnits
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section Pins

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))

open Pointwise in

theorem galPermSL_asIdeal
    (w : ↥{w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))}) :
    (galPermSL K L ↑S σ w).1.asIdeal = Ideal.map ((galRestrict (𝓞 K) K L (𝓞 L)) σ) w.1.asIdeal := by
  have hfun : ∀ x : 𝓞 L, σ • x = (galRestrict (𝓞 K) K L (𝓞 L)) σ x := by
    intro x
    have hcoe : ((σ • x : 𝓞 L) : L) = (((galRestrict (𝓞 K) K L (𝓞 L)) σ x : 𝓞 L) : L) := by
      rw [show ((σ • x : 𝓞 L) : L) = σ • (x : L) from rfl, AlgEquiv.smul_def]
      exact (algebraMap_galRestrict_apply (𝓞 K) σ x).symm
    exact Subtype.ext hcoe
  show σ • w.1.asIdeal = Ideal.map ((galRestrict (𝓞 K) K L (𝓞 L)) σ) w.1.asIdeal
  rw [Ideal.pointwise_smul_def]
  show Ideal.span _ = Ideal.span _
  exact congrArg Ideal.span (congrArg₂ Set.image (funext hfun) rfl)

end Pins
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section PhiPow

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (W : Set (HeightOneSpectrum (𝓞 L)))
  (Φ : ↥(W.unit L) ≃* ↥(W.unit L)) (hΦ : ∀ u, (((Φ u : Lˣ) : L)) = σ (((u : Lˣ) : L)))
include hΦ

theorem phi_pow_coe (k : ℕ) (u : ↥(W.unit L)) :
    ((((Φ ^ k) u : ↥(W.unit L)) : Lˣ) : L) = (σ ^ k) (((u : Lˣ) : L)) := by
  induction k generalizing u with
  | zero =>
      simp only [pow_zero]
      rfl
  | succ k ih =>
      have h1 : (Φ ^ (k + 1)) u = (Φ ^ k) (Φ u) := by
        rw [pow_succ]
        rfl
      rw [h1, ih (Φ u), hΦ]
      show (σ ^ k) (σ (((u : Lˣ) : L))) = (σ ^ (k + 1)) (((u : Lˣ) : L))
      rw [pow_succ]
      rfl

theorem phi_pow_card : Φ ^ Nat.card (L ≃ₐ[K] L) = 1 := by
  refine MulEquiv.ext fun u => Subtype.ext (Units.ext ?_)
  rw [phi_pow_coe K L σ W Φ hΦ, pow_card_eq_one']
  rfl

end PhiPow
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

section Main

theorem uherb_impl
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (W : Set (HeightOneSpectrum (𝓞 L))) (hW : W = {w | w.under (𝓞 K) ∈ ↑S})

    (Φ : ↥(W.unit L) ≃* ↥(W.unit L))
    (hΦ : ∀ u, (((Φ u : Lˣ) : L)) = σ (((u : Lˣ) : L)))

    (d : Additive ↥(W.unit L) →+ Additive ↥(W.unit L))
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul (Φ u) - Additive.ofMul u)
    (N : Additive ↥(W.unit L) →+ Additive ↥(W.unit L))
    (hN : ∀ u, N (Additive.ofMul u)
          = ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), Additive.ofMul ((Φ ^ i) u))

    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v})
    (si : InfinitePlace K → ℕ)
    (hsi : ∀ v, si v = Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) * Nat.card (L ≃ₐ[K] L)
        = ((∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v)
            * ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / si v)
          * Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker)
      ∧ Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) ≠ 0 := by
  subst hW
  have hn : 0 < Nat.card (L ≃ₐ[K] L) := Nat.card_pos
  haveI := finite_placesOver K L S

  have hΦn : Φ ^ Nat.card (L ≃ₐ[K] L) = 1 := phi_pow_card K L σ _ Φ hΦ
  have hα : MulEquiv.toAdditive Φ ^ Nat.card (L ≃ₐ[K] L) = 1 := by
    rw [toAdditive_mulAut_pow, hΦn]; rfl

  obtain rfl : d = (ofAddAut (MulEquiv.toAdditive Φ) (Nat.card (L ≃ₐ[K] L)) hα).derive :=
    AddMonoidHom.ext fun x => hd (Additive.toMul x)
  obtain rfl : N = (ofAddAut (MulEquiv.toAdditive Φ) (Nat.card (L ≃ₐ[K] L)) hα).norm := by
    refine AddMonoidHom.ext fun x => (hN (Additive.toMul x)).trans ?_
    rw [ofAddAut_norm_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [toAdditive_mulAut_pow]; rfl
  obtain rfl : sf = finSplit K L := funext fun v => hsf v
  obtain rfl : si = infSplit K L := funext fun v => hsi v

  have hψ : addAutQuotTorsion (MulEquiv.toAdditive Φ) ^ Nat.card (L ≃ₐ[K] L) = 1 :=
    addAutQuotTorsion_pow_eq_one _ hα
  have hrank := M4aHerbrand.sUnitQuot_fixedRank_eq K L σ S _ rfl Φ hΦ
    (AddCommGroup.torsion _) torsion_mem_iff (addAutQuotTorsion (MulEquiv.toAdditive Φ)) (fun _ => rfl)
    (galPermSL K L ↑S σ) (galPermSL_asIdeal K L σ S) (placePermAut K L σ ↑S) (fun _ _ => rfl)
    (MulAction.toPerm σ) (fun _ => rfl) (infPermAut K L σ) (fun _ _ => rfl)

  have key := UnitLatticeAssembly.hU_of_fixedRanks K L σ hσ S (addAutQuotTorsion (MulEquiv.toAdditive Φ)) hψ
    (fun e _ => hrank e)
  have hQ₁ := (FGTateFinite.tateCard_ne_zero_of_fg (addAutQuotTorsion (MulEquiv.toAdditive Φ)) hn hψ).2
  have hofq : ofAddAut (addAutQuotTorsion (MulEquiv.toAdditive Φ)) (Nat.card (L ≃ₐ[K] L)) hψ
      = ofAddAutQuotTorsion (MulEquiv.toAdditive Φ) hα := rfl
  rw [hofq, tateCard₀_ofAddAutQuotTorsion_eq, tateCard₁_ofAddAutQuotTorsion_eq] at key
  rw [hofq, tateCard₁_ofAddAutQuotTorsion_eq] at hQ₁

  have main := tateCard_eq_transport_of_finite_stable_subgroup
    (ofAddAut (MulEquiv.toAdditive Φ) (Nat.card (L ≃ₐ[K] L)) hα) (AddCommGroup.torsion _)
    (torsion_stable_derive _ hα) (torsion_stable_norm _ hα) _ _ key hQ₁
  exact ⟨main, (FGTateFinite.tateCard_ne_zero_of_fg (MulEquiv.toAdditive Φ) hn hα).1⟩

end Main
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end M4aHerbrand.UherbSol
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.UherbSol"
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData"

end
p2m_reactivate "P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.CyclicRational P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandPair P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.HerbrandTriple P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.LocalUnitsCohomology P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.InducedModule P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.FGTateFinite P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aLocalCFT.SemilocalHerbrand P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.IdempotentCycle P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.PlacePermLattice P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.RationalData P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.M4aHerbrand.UherbSol"

open NumberField IsDedekindDomain in
theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (W : Set (HeightOneSpectrum (𝓞 L))) (hW : W = {w | w.under (𝓞 K) ∈ ↑S})

    (Φ : ↥(W.unit L) ≃* ↥(W.unit L))
    (hΦ : ∀ u, (((Φ u : Lˣ) : L)) = σ (((u : Lˣ) : L)))

    (d : Additive ↥(W.unit L) →+ Additive ↥(W.unit L))
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul (Φ u) - Additive.ofMul u)
    (N : Additive ↥(W.unit L) →+ Additive ↥(W.unit L))
    (hN : ∀ u, N (Additive.ofMul u)
          = ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), Additive.ofMul ((Φ ^ i) u))

    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v})
    (si : InfinitePlace K → ℕ)
    (hsi : ∀ v, si v = Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) * Nat.card (L ≃ₐ[K] L)
        = ((∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v)
            * ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / si v)
          * Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker)
      ∧ Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) ≠ 0 :=
  M4aHerbrand.UherbSol.uherb_impl K L σ hσ S W hW Φ hΦ d hd N hN sf hsf si hsi

end S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd
end P2MW
export P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd (solution)
