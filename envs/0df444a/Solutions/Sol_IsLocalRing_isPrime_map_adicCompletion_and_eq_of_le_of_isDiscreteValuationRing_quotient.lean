-- Prove2me | solution 1 for IsLocalRing.isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fb0f78af-9424-57a0-ab67-bfeb830d5c5b

import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient

set_option autoImplicit false

open IsLocalRing

namespace BRDISTb

section

variable {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (Q : Ideal R) [Q.IsPrime] [IsDomain (R ⧸ Q)] [IsDiscreteValuationRing (R ⧸ Q)]

local notation "Rh" => AdicCompletion (maximalIdeal R) R
local notation "Dh" => AdicCompletion (maximalIdeal (R ⧸ Q)) (R ⧸ Q)

theorem maxD_eq : maximalIdeal (R ⧸ Q) = (maximalIdeal R).map (Ideal.Quotient.mk Q) :=
  (map_maximalIdeal_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective).symm

theorem pow_le_comap (n : ℕ) :
    (maximalIdeal R) ^ n ≤ ((maximalIdeal (R ⧸ Q)) ^ n).comap (Ideal.Quotient.mk Q) := by
  rw [maxD_eq Q, ← Ideal.map_pow]
  exact Ideal.le_comap_map

noncomputable def lvl (n : ℕ) : Rh →+* (R ⧸ Q) ⧸ (maximalIdeal (R ⧸ Q)) ^ n :=
  (Ideal.quotientMap ((maximalIdeal (R ⧸ Q)) ^ n) (Ideal.Quotient.mk Q) (pow_le_comap Q n)).comp
    (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom

theorem lvl_apply (n : ℕ) (x : Rh) :
    lvl Q n x = Ideal.quotientMap ((maximalIdeal (R ⧸ Q)) ^ n) (Ideal.Quotient.mk Q)
      (pow_le_comap Q n) (AdicCompletion.evalₐ (maximalIdeal R) n x) := rfl

theorem lvl_mk (n : ℕ) (a : AdicCompletion.AdicCauchySequence (maximalIdeal R) R) :
    lvl Q n (AdicCompletion.mk (maximalIdeal R) R a) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk Q (a n)) := by
  rw [lvl_apply, AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]

theorem lvl_of (n : ℕ) (r : R) :
    lvl Q n (algebraMap R Rh r) = Ideal.Quotient.mk _ (Ideal.Quotient.mk Q r) := by
  rw [lvl_apply, AdicCompletion.evalₐ_algebraMap, Ideal.quotientMap_mk]

theorem lvl_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal (R ⧸ Q)) hle).comp (lvl Q n) = lvl Q m := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal R) R x
  rw [RingHom.comp_apply, lvl_mk, lvl_mk]
  show Ideal.Quotient.factor _ _ = _
  rw [Ideal.Quotient.factor_mk]
  have h := congrArg (Ideal.quotientMap ((maximalIdeal (R ⧸ Q)) ^ m) (Ideal.Quotient.mk Q)
    (pow_le_comap Q m)) (AdicCompletion.Ideal.mk_eq_mk (maximalIdeal R) hle a)
  rwa [Ideal.quotientMap_mk, Ideal.quotientMap_mk] at h

noncomputable def psi : Rh →+* Dh :=
  AdicCompletion.liftRingHom (maximalIdeal (R ⧸ Q)) (lvl Q) (fun hle => lvl_compat Q hle)

theorem evalₐ_psi (n : ℕ) (x : Rh) :
    AdicCompletion.evalₐ (maximalIdeal (R ⧸ Q)) n (psi Q x) = lvl Q n x :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ n x

theorem psi_of (r : R) :
    psi Q (algebraMap R Rh r) = algebraMap (R ⧸ Q) Dh (Ideal.Quotient.mk Q r) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_psi, lvl_of, AdicCompletion.evalₐ_algebraMap]

theorem psi_comp :
    (psi Q).comp (algebraMap R Rh) = (algebraMap (R ⧸ Q) Dh).comp (Ideal.Quotient.mk Q) :=
  RingHom.ext (psi_of Q)

theorem map_map_psi :
    ((maximalIdeal R).map (algebraMap R Rh)).map (psi Q) =
      (maximalIdeal (R ⧸ Q)).map (algebraMap (R ⧸ Q) Dh) := by
  rw [Ideal.map_map, psi_comp, ← Ideal.map_map, ← maxD_eq]

theorem psi_surjective : Function.Surjective (psi Q) := by
  haveI : IsAdicComplete ((maximalIdeal R).map (algebraMap R Rh)) Rh :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) Rh).mpr
      (AdicCompletion.isAdicComplete AdicCompletion.maximalIdeal_fg)
  haveI hD : IsAdicComplete ((maximalIdeal (R ⧸ Q)).map (algebraMap (R ⧸ Q) Dh)) Dh :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal (R ⧸ Q)) Dh).mpr
      (AdicCompletion.isAdicComplete AdicCompletion.maximalIdeal_fg)
  haveI : IsHausdorff (((maximalIdeal R).map (algebraMap R Rh)).map (psi Q)) Dh := by
    rw [map_map_psi]; infer_instance
  refine surjective_of_mk_map_comp_surjective
    (I := (maximalIdeal R).map (algebraMap R Rh)) (psi Q) ?_
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨d, w, hw, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add (maximalIdeal (R ⧸ Q))
    AdicCompletion.maximalIdeal_fg 1 y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨algebraMap R Rh r, ?_⟩
  rw [RingHom.comp_apply, psi_of, Ideal.Quotient.mk_eq_mk_iff_sub_mem, map_map_psi]
  rw [pow_one] at hw
  have : algebraMap (R ⧸ Q) Dh (Ideal.Quotient.mk Q r) -
      (algebraMap (R ⧸ Q) Dh (Ideal.Quotient.mk Q r) + w) = -w := by ring
  rw [this]
  exact neg_mem hw

theorem le_ker : Q.map (algebraMap R Rh) ≤ RingHom.ker (psi Q) := by
  rw [Ideal.map_le_iff_le_comap]
  intro q hq
  rw [Ideal.mem_comap, RingHom.mem_ker, psi_of, Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]

theorem of_eq_algebraMap (r : R) : AdicCompletion.of (maximalIdeal R) R r = algebraMap R Rh r := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem map_mkQ_eq_zero (x : Rh) (hx : psi Q x = 0) :
    AdicCompletion.map (maximalIdeal R) (Submodule.mkQ Q) x = 0 := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal R) R x
  have ha := hx
  rw [AdicCompletion.map_mk]
  refine AdicCompletion.ext fun n => ?_
  have h1 : lvl Q n (AdicCompletion.mk (maximalIdeal R) R a) = 0 := by
    rw [← evalₐ_psi, ha, map_zero]
  rw [lvl_mk, Ideal.Quotient.eq_zero_iff_mem, maxD_eq Q, ← Ideal.map_pow] at h1
  simp only [AdicCompletion.val_zero, Pi.zero_apply, AdicCompletion.mk_apply_coe, Submodule.mkQ_apply,
    AdicCompletion.AdicCauchySequence.map_apply_coe]
  rw [Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk]
  exact h1

theorem ker_le : RingHom.ker (psi Q) ≤ Q.map (algebraMap R Rh) := by
  intro x hx
  have h1 := map_mkQ_eq_zero Q x hx
  have hex := AdicCompletion.map_exact (I := maximalIdeal R) (f := Q.subtype) (g := Q.mkQ)
    (Submodule.injective_subtype Q) (LinearMap.exact_subtype_mkQ Q) (Submodule.mkQ_surjective Q)
  obtain ⟨y, hy⟩ := (hex x).mp h1
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite (maximalIdeal R) (↥Q) y
  rw [← hy]
  clear hy
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul r q =>
      rw [AdicCompletion.ofTensorProduct_tmul, LinearMap.map_smul, AdicCompletion.map_of,
        Submodule.subtype_apply, of_eq_algebraMap]
      change r * algebraMap R Rh (q : R) ∈ Q.map (algebraMap R Rh)
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ q.2)
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

theorem ker_eq : RingHom.ker (psi Q) = Q.map (algebraMap R Rh) :=
  le_antisymm (ker_le Q) (le_ker Q)

theorem main :
    (Q.map (algebraMap R Rh)).IsPrime ∧
    ∀ P : Ideal Rh, P.IsPrime → Q.map (algebraMap R Rh) ≤ P → ¬ P.IsMaximal →
      P = Q.map (algebraMap R Rh) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R ⧸ Q)
  obtain ⟨hdom, hdvr, -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
      (R ⧸ Q) ϖ hϖ
  rw [← ker_eq Q]
  refine ⟨RingHom.ker_isPrime (psi Q), fun P hP hle hmax => ?_⟩
  haveI := hP
  have hP' : (P.map (psi Q)).IsPrime := Ideal.map_isPrime_of_surjective (psi_surjective Q) hle
  have hcomap : (P.map (psi Q)).comap (psi Q) = P := by
    rw [Ideal.comap_map_of_surjective _ (psi_surjective Q), sup_eq_left]
    exact hle
  by_cases hbot : P.map (psi Q) = ⊥
  · rw [← hcomap, hbot]; rfl
  · exfalso
    apply hmax
    haveI hm : (P.map (psi Q)).IsMaximal := IsPrime.to_maximal_ideal hbot
    rw [← hcomap]
    exact Ideal.comap_isMaximal_of_surjective _ (psi_surjective Q)

end

end BRDISTb

theorem solution
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (Q : Ideal R) [Q.IsPrime] [IsDomain (R ⧸ Q)] [IsDiscreteValuationRing (R ⧸ Q)] :
    (Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).IsPrime ∧
    ∀ P : Ideal (AdicCompletion (maximalIdeal R) R), P.IsPrime →
      Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≤ P → ¬ P.IsMaximal →
      P = Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  BRDISTb.main Q

end S_IsLocalRing_isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient
end P2MW
export P2MW.S_IsLocalRing_isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient (solution)
