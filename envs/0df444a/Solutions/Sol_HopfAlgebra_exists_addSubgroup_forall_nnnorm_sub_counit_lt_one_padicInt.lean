-- Prove2me | solution 1 for HopfAlgebra.exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f67eb21a-8537-5149-b5b5-b35956f733b5

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt

set_option autoImplicit false

open Coalgebra
open scoped NNReal

namespace S17RedSubgroup

variable {p : ℕ} [Fact p.Prime] {H : Type} [CommRing H]
  [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H]

local notation "Kp" => PadicAlgCl p
local notation "Pt" => WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)
local notation "vv" => (Valued.v : Valuation (PadicAlgCl p) ℝ≥0)

abbrev Conn (f : Pt) : Prop :=
  ∀ h : H, vv (f h - algebraMap ℤ_[p] Kp (counit h)) < 1

theorem mul_lt_one_aux {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
  lt_of_le_of_lt (mul_le_mul_right hb a) (by rwa [mul_one])

theorem mul_lt_one_aux' {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a ≤ 1) (hb : b < 1) : a * b < 1 := by
  rw [mul_comm]; exact mul_lt_one_aux hb ha

theorem v_eq_nnnorm (x : Kp) : vv x = ‖x‖₊ := rfl

theorem v_algebraMap_le_one (r : ℤ_[p]) : vv (algebraMap ℤ_[p] Kp r) ≤ 1 := by
  have h : ‖algebraMap ℤ_[p] Kp r‖ ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] Kp]
    change ‖((r : ℚ_[p]) : Kp)‖ ≤ 1
    rw [PadicAlgCl.norm_extends]
    exact PadicInt.norm_le_one r
  have h2 : ‖algebraMap ℤ_[p] Kp r‖₊ ≤ 1 := h
  exact h2

theorem v_apply_le_one (f : Pt) (h : H) : vv (f h) ≤ 1 := by
  classical
  have hint : IsIntegral ℤ_[p] ((WithConv.ofConv f : H →ₐ[ℤ_[p]] Kp) h) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) h).map _
  obtain ⟨P, hPm, hPev⟩ := hint
  by_contra hgt
  rw [not_le] at hgt
  have hy0 : vv (f h) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have hsum : ∑ i ∈ Finset.range (P.natDegree + 1),
      algebraMap ℤ_[p] Kp (P.coeff i) * f h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hPev
  rw [Finset.sum_range_succ, hPm.coeff_natDegree, map_one, one_mul] at hsum
  have hyd : f h ^ P.natDegree
      = -∑ i ∈ Finset.range P.natDegree, algebraMap ℤ_[p] Kp (P.coeff i) * f h ^ i :=
    eq_neg_of_add_eq_zero_right hsum
  have hlt : vv (∑ i ∈ Finset.range P.natDegree, algebraMap ℤ_[p] Kp (P.coeff i) * f h ^ i)
        < vv (f h) ^ P.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    have hi' : i < P.natDegree := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc vv (algebraMap ℤ_[p] Kp (P.coeff i)) * vv (f h) ^ i
        ≤ 1 * vv (f h) ^ i := by
          apply mul_le_mul_left
          exact v_algebraMap_le_one (P.coeff i)
      _ = vv (f h) ^ i := one_mul _
      _ < vv (f h) ^ P.natDegree := pow_lt_pow_right₀ hgt hi'
  have hcontra : vv (f h ^ P.natDegree) < vv (f h) ^ P.natDegree := by
    rw [hyd, Valuation.map_neg]
    exact hlt
  rw [Valuation.map_pow] at hcontra
  exact lt_irrefl _ hcontra

theorem conn_one : Conn (1 : Pt) := by
  intro h
  rw [AlgHom.convOne_apply, sub_self, map_zero]
  exact zero_lt_one

theorem convMul_apply_repr (f g : Pt) {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr ℤ_[p] h ι𝓡) :
    (f * g) h = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  have := congrArg (fun (φ : WithConv (H →ₗ[ℤ_[p]] Kp)) => (WithConv.ofConv φ) h)
    (AlgHom.toLinearMap_convMul f g)
  simp only [WithConv.ofConv_toConv, AlgHom.toLinearMap_apply] at this
  rw [this, Coalgebra.Repr.convMul_apply 𝓡]
  rfl

theorem counit_repr {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr ℤ_[p] h ι𝓡) :
    algebraMap ℤ_[p] Kp (counit h) =
      ∑ i ∈ 𝓡.index, algebraMap ℤ_[p] Kp (counit (𝓡.left i)) *
        algebraMap ℤ_[p] Kp (counit (𝓡.right i)) := by
  have h1 := Coalgebra.sum_counit_smul 𝓡
  have h2 : (counit (R := ℤ_[p]) h) = ∑ i ∈ 𝓡.index, counit (R := ℤ_[p]) (𝓡.left i) * counit (R := ℤ_[p]) (𝓡.right i) := by
    conv_lhs => rw [← h1]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [h2, map_sum]
  simp [map_mul]

theorem apply_repr (g : Pt) {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr ℤ_[p] h ι𝓡) :
    (g h : Kp) = ∑ i ∈ 𝓡.index, algebraMap ℤ_[p] Kp (counit (𝓡.left i)) * g (𝓡.right i) := by
  have h1 := Coalgebra.sum_counit_smul 𝓡
  conv_lhs => rw [← h1]
  simp [map_sum, map_smul, Algebra.smul_def]

theorem conn_mul {f g : Pt} (hf : Conn f) (hg : Conn g) : Conn (f * g) := by
  classical
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary ℤ_[p] h
  rw [convMul_apply_repr f g 𝓡, counit_repr 𝓡, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ (by exact one_ne_zero) fun i _ => ?_
  have e1 : f (𝓡.left i) * g (𝓡.right i) -
      algebraMap ℤ_[p] Kp (counit (𝓡.left i)) * algebraMap ℤ_[p] Kp (counit (𝓡.right i)) =
      (f (𝓡.left i) - algebraMap ℤ_[p] Kp (counit (𝓡.left i))) * g (𝓡.right i) +
      algebraMap ℤ_[p] Kp (counit (𝓡.left i)) *
        (g (𝓡.right i) - algebraMap ℤ_[p] Kp (counit (𝓡.right i))) := by ring
  rw [e1]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    exact mul_lt_one_aux (hf _) (v_apply_le_one g _)
  · rw [map_mul]
    exact mul_lt_one_aux' (v_algebraMap_le_one _) (hg _)

theorem conn_inv {f f' : Pt} (hf : Conn f) (hff' : f * f' = 1) : Conn f' := by
  classical
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary ℤ_[p] h
  have h1 : algebraMap ℤ_[p] Kp (counit h) = ∑ i ∈ 𝓡.index, f (𝓡.left i) * f' (𝓡.right i) := by
    rw [← convMul_apply_repr f f' 𝓡, hff', AlgHom.convOne_apply]
  rw [apply_repr f' 𝓡, h1, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ (by exact one_ne_zero) fun i _ => ?_
  rw [← sub_mul, map_mul, ← Valuation.map_neg, neg_sub]
  exact mul_lt_one_aux (hf _) (v_apply_le_one f' _)

noncomputable def translate (σ : Kp ≃ₐ[ℚ_[p]] Kp) (f : Pt) : Pt :=
  WithConv.toConv
    { toRingHom := (σ : Kp →+* Kp).comp (WithConv.ofConv f : H →ₐ[ℤ_[p]] Kp).toRingHom
      commutes' := fun r => by
        change σ ((WithConv.ofConv f : H →ₐ[ℤ_[p]] Kp) (algebraMap ℤ_[p] H r)) = algebraMap ℤ_[p] Kp r
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] Kp]
        exact σ.commutes (r : ℚ_[p]) }

theorem translate_apply (σ : Kp ≃ₐ[ℚ_[p]] Kp) (f : Pt) (h : H) : translate σ f h = σ (f h) := rfl

theorem v_algEquiv (σ : Kp ≃ₐ[ℚ_[p]] Kp) (y : Kp) : vv (σ y) = vv y := by
  rw [v_eq_nnnorm, v_eq_nnnorm]
  ext
  exact (spectralNorm_eq_of_equiv σ y).symm

theorem conn_translate (σ : Kp ≃ₐ[ℚ_[p]] Kp) {f : Pt} (hf : Conn f) : Conn (translate σ f) := by
  intro h
  rw [translate_apply]
  have : σ (f h) - algebraMap ℤ_[p] Kp (counit h) = σ (f h - algebraMap ℤ_[p] Kp (counit h)) := by
    rw [map_sub, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] Kp, AlgEquiv.commutes]
  rw [this, v_algEquiv]
  exact hf h

theorem v_sub_lt_one_of_inertia {σ : Kp ≃ₐ[ℚ_[p]] Kp}
    (hσ : σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) {a : Kp} (ha : vv a ≤ 1) :
    vv (σ a - a) < 1 := by
  have hmem : a ∈ padicIntegers p := ha
  have h := (ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn (padicIntegers p) hσ hmem).2
  have hiso := Valuation.isEquiv_valuation_valuationSubring vv
  exact (hiso.lt_one_iff_lt_one).mpr h

theorem conn_displacement {σ : Kp ≃ₐ[ℚ_[p]] Kp} (hσ : σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p])
    {f f' : Pt} (hff' : f * f' = 1) : Conn (translate σ f * f') := by
  classical
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary ℤ_[p] h
  have h1 : algebraMap ℤ_[p] Kp (counit h) = ∑ i ∈ 𝓡.index, f (𝓡.left i) * f' (𝓡.right i) := by
    rw [← convMul_apply_repr f f' 𝓡, hff', AlgHom.convOne_apply]
  rw [convMul_apply_repr _ _ 𝓡, h1, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ (by exact one_ne_zero) fun i _ => ?_
  rw [translate_apply, ← sub_mul, map_mul]
  exact mul_lt_one_aux (v_sub_lt_one_of_inertia hσ (v_apply_le_one f _)) (v_apply_le_one f' _)

end S17RedSubgroup

open S17RedSubgroup in

theorem solution
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (M : Type) [AddCommGroup M]
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (act : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → M → M)
    (hact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H, g h = σ (f h)) → e g = act σ (e f)) :
    ∃ K : AddSubgroup M,
      (∀ x : M, x ∈ K ↔ ∃ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), e f = x ∧
        ∀ h : H, ‖f h - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit (R := ℤ_[p]) h)‖₊ < 1) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : M), x ∈ K → act σ x ∈ K) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ x : M, act σ x - x ∈ K) := by
  classical

  have he1 : e 1 = 0 := by
    have h := he 1 1
    rw [one_mul] at h
    have h2 : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hsymm_add : ∀ x y : M, e.symm (x + y) = e.symm x * e.symm y := by
    intro x y; apply e.injective; rw [he]; simp
  have hinv : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), f * e.symm (-e f) = 1 := by
    intro f
    apply e.injective
    rw [he, Equiv.apply_symm_apply, add_neg_cancel, he1]

  let K : AddSubgroup M :=
    { carrier := {x | ∃ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), e f = x ∧ Conn f}
      zero_mem' := ⟨1, he1, conn_one⟩
      add_mem' := by
        rintro x y ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
        exact ⟨f * g, he f g, conn_mul hf hg⟩
      neg_mem' := by
        rintro x ⟨f, rfl, hf⟩
        exact ⟨e.symm (-e f), Equiv.apply_symm_apply _ _, conn_inv hf (hinv f)⟩ }
  refine ⟨K, fun x => Iff.rfl, ?_, ?_⟩
  · rintro σ x ⟨f, rfl, hf⟩
    refine ⟨translate σ f, ?_, conn_translate σ hf⟩
    exact hact σ f (translate σ f) (fun h => rfl)
  · intro σ hσ x
    obtain ⟨f, rfl⟩ := e.surjective x
    refine ⟨translate σ f * e.symm (-e f), ?_, conn_displacement hσ (hinv f)⟩
    rw [he, Equiv.apply_symm_apply, hact σ f (translate σ f) (fun h => rfl), sub_eq_add_neg]

end S_HopfAlgebra_exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt
end P2MW
export P2MW.S_HopfAlgebra_exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt (solution)
