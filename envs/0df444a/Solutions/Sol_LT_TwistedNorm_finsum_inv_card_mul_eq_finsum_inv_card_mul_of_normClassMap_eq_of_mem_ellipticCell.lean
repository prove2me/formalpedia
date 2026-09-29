-- Prove2me | solution 1 for LT.TwistedNorm.finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/502e6b68-05a2-5e32-9a6b-61f84193505f

import Theorems.Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell

set_option autoImplicit false

p2m_open "LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm"

namespace LT
p2m_export "LT" "mk TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.normClassMap TwistedNorm.IsNormClass"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell sigmaPartialNorm sigmaPartialNorm_succ' sigmaNormPow sigmaNormPow_def coe_sigmaNormPow_units_eq_algebraMap_norm SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map IsNormRep normRep isNormRep_normRep normClassMap normClassMap_mk normClassMap_mk_eq_of_isNormRep IsNormClass isNormClass_mk_iff"
namespace EllipticWeights
p2m_open "LT.TwistedNorm LT"

section GL2

variable {K : Type*} [Field K]

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

theorem scalar_mul_comm (c : Kˣ) (g : GL (Fin 2) K) : sc c * g = g * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : K) * (g : Matrix (Fin 2) (Fin 2) K) =
    (g : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (c : K)
  exact (Matrix.scalar_commute (c : K) (fun r => Commute.all _ r) _).eq

theorem conj_scalar_mul (c : Kˣ) (g h : GL (Fin 2) K) :
    h⁻¹ * (sc c * g) * h = sc c * (h⁻¹ * g * h) := by
  rw [show h⁻¹ * (sc c * g) * h = (h⁻¹ * sc c) * (g * h) by simp only [mul_assoc],
    ← scalar_mul_comm c h⁻¹]
  simp only [mul_assoc]

theorem scalar_mul_mem_ellipticCell (a : Kˣ) {γ : GL (Fin 2) K}
    (hγ : γ ∈ AutomorphicForm.ellipticCell K) :
    sc a * γ ∈ AutomorphicForm.ellipticCell K := by
  rw [AutomorphicForm.mem_ellipticCell_iff] at hγ ⊢
  intro r hr
  apply hγ (r / a)
  have hval : ((sc a * γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (a : K) • (γ : Matrix (Fin 2) (Fin 2) K) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.diagonal_mul]
  rw [hval] at hr
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at hr ⊢
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin,
    smul_eq_mul] at hr ⊢
  have ha : (a : K) ≠ 0 := a.ne_zero
  have key : (r / a) ^ 2 - Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) * (r / a) +
      Matrix.det (γ : Matrix (Fin 2) (Fin 2) K) =
      (r ^ 2 - (a : K) * Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) * r +
        (a : K) ^ 2 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) K)) / (a : K) ^ 2 := by
    field_simp
  rw [key, hr, zero_div]

def stab (γ₀ : GL (Fin 2) K) : Subgroup Kˣ where
  carrier := {a : Kˣ | ∃ h : GL (Fin 2) K, sc a * γ₀ = h⁻¹ * γ₀ * h}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hha⟩ ⟨hb, hhb⟩
    refine ⟨ha * hb, ?_⟩
    rw [map_mul, mul_assoc, hhb, ← conj_scalar_mul, hha]
    group
  inv_mem' := by
    rintro a ⟨h, hh⟩
    have e1 : h * (sc a * γ₀) * h⁻¹ = γ₀ := by rw [hh]; group
    have e2 : h * (sc a * γ₀) * h⁻¹ = sc a * (h * γ₀ * h⁻¹) := by
      simpa only [inv_inv] using conj_scalar_mul a γ₀ h⁻¹
    refine ⟨h⁻¹, ?_⟩
    rw [inv_inv]
    calc sc a⁻¹ * γ₀ = sc a⁻¹ * (h * (sc a * γ₀) * h⁻¹) := by rw [e1]
      _ = sc a⁻¹ * (sc a * (h * γ₀ * h⁻¹)) := by rw [e2]
      _ = h * γ₀ * h⁻¹ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem mem_stab_iff (γ₀ : GL (Fin 2) K) (a : Kˣ) :
    a ∈ stab γ₀ ↔ ∃ h : GL (Fin 2) K, sc a * γ₀ = h⁻¹ * γ₀ * h := Iff.rfl

theorem sq_eq_one_of_mem_stab {γ₀ : GL (Fin 2) K} {a : Kˣ} (ha : a ∈ stab γ₀) : a = 1 ∨ a = -1 := by
  obtain ⟨h, hh⟩ := ha
  have hdet : Matrix.GeneralLinearGroup.det (sc a * γ₀) = Matrix.GeneralLinearGroup.det (h⁻¹ * γ₀ * h) :=
    congrArg _ hh
  rw [map_mul, map_mul, map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hc : (Matrix.GeneralLinearGroup.det h)⁻¹ * Matrix.GeneralLinearGroup.det γ₀ *
      Matrix.GeneralLinearGroup.det h = Matrix.GeneralLinearGroup.det γ₀ := by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hc] at hdet
  have h1 : a ^ 2 = 1 := mul_right_cancel (hdet.trans (one_mul _).symm)
  have h2 : (a : K) ^ 2 = 1 := by
    have := congrArg Units.val h1
    simpa using this
  rcases sq_eq_one_iff.mp h2 with h | h
  · left; exact Units.ext (by simpa using h)
  · right; exact Units.ext (by simpa using h)

theorem stab_finite (γ₀ : GL (Fin 2) K) : (stab γ₀ : Set Kˣ).Finite :=
  ((Set.finite_singleton (-1 : Kˣ)).insert 1).subset fun a ha => by
    rcases sq_eq_one_of_mem_stab ha with rfl | rfl <;> simp

scoped instance stab_finite_inst (γ₀ : GL (Fin 2) K) : Finite (stab γ₀) := (stab_finite γ₀).to_subtype

theorem mk_scalar_mul_eq_iff (γ₀ : GL (Fin 2) K) (a b : Kˣ) :
    ConjClasses.mk (sc a * γ₀) = ConjClasses.mk (sc b * γ₀) ↔ a⁻¹ * b ∈ stab γ₀ := by
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff, mem_stab_iff]
  constructor
  · rintro ⟨c, hc⟩
    have e : c * (sc a * γ₀) * c⁻¹ = sc a * (c * γ₀ * c⁻¹) := by
      simpa only [inv_inv] using conj_scalar_mul a γ₀ c⁻¹
    refine ⟨c⁻¹, ?_⟩
    rw [inv_inv, map_mul, mul_assoc, ← hc, e, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  · rintro ⟨h, hh⟩
    refine ⟨h⁻¹, ?_⟩
    rw [inv_inv, conj_scalar_mul, ← hh, ← mul_assoc, ← map_mul, mul_inv_cancel_left]

end GL2

section NormScalar

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

omit [FiniteDimensional F L] [IsGalois F L] in
theorem map_scalar (u : Lˣ) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) (sc u) = sc (Units.map ((σ : L →+* L) : L →* L) u) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

omit [FiniteDimensional F L] [IsGalois F L] in

theorem sigmaPartialNorm_scalar_mul (u : Lˣ) (δ : GL (Fin 2) L) (r : ℕ) :
    sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (sc u * δ) r =
      sc (sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) u r) *
        sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul, map_scalar,
        map_mul]

      rw [← mul_assoc, mul_assoc (sc u) δ, ← scalar_mul_comm, ← mul_assoc, ← map_mul, mul_assoc]

theorem map_algebraMap_scalar_norm (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap F L) (sc (Units.map (Algebra.norm F : L →* F) u)) =
      sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Units.coe_map]
    rw [coe_sigmaNormPow_units_eq_algebraMap_norm hgen u]
  · simp [hij, Matrix.scalar_apply]

theorem isNormRep_scalar_mul (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) F} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (u : Lˣ) :
    IsNormRep σ (sc (Units.map (Algebra.norm F : L →* F) u) * γ) (sc u * δ) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_def, sigmaPartialNorm_scalar_mul, ← sigmaNormPow_def, ← sigmaNormPow_def, map_mul,
    map_algebraMap_scalar_norm hgen, ← hP, ← conj_scalar_mul]

theorem isNormRep_of_normClassMap_eq (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) : IsNormRep σ γ δ := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) c⁻¹, ?_⟩
  rw [← hc, map_mul, map_mul, map_inv, ← hP]
  group

theorem normClassMap_scalar_mul (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) (u : Lˣ) :
    normClassMap hgen (SigmaConjClasses.mk σ (sc u * δ)) =
      ConjClasses.mk (sc (Units.map (Algebra.norm F : L →* F) u) * γ) :=
  normClassMap_mk_eq_of_isNormRep hgen (isNormRep_scalar_mul hgen (isNormRep_of_normClassMap_eq hgen h) u)

theorem normClassMap_mk_sigmaConj (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ h : GL (Fin 2) L) :
    normClassMap hgen (SigmaConjClasses.mk σ (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) =
      normClassMap hgen (SigmaConjClasses.mk σ δ) := by
  congr 1
  exact (SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨h, rfl⟩).symm

end NormScalar

end LT.TwistedNorm.EllipticWeights
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm"
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT"

namespace LT
p2m_export "LT" "mk TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.normClassMap TwistedNorm.IsNormClass"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell sigmaPartialNorm sigmaPartialNorm_succ' sigmaNormPow sigmaNormPow_def coe_sigmaNormPow_units_eq_algebraMap_norm SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map IsNormRep normRep isNormRep_normRep normClassMap normClassMap_mk normClassMap_mk_eq_of_isNormRep IsNormClass isNormClass_mk_iff"
namespace EllipticWeights
p2m_open "LT.TwistedNorm LT"

section Weights

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ : L ≃ₐ[K] L}

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)
local notation "σ'" => Matrix.GeneralLinearGroup.map (σ : L →+* L)

variable (K L) in

noncomputable abbrev nu : Lˣ →* Kˣ := Units.map (Algebra.norm K : L →* K)

variable (σ) in

abbrev Rgrp : Subgroup Lˣ := (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range

omit [FiniteDimensional K L] [IsGalois K L] in
theorem coe_R_apply (w : Lˣ) :
    ((((Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ) w : Lˣ)) : L) = σ (w : L) / (w : L) := by
  rw [MonoidHom.div_apply, Units.val_div_eq_div_val, Units.coe_map, MonoidHom.id_apply]
  rfl

omit [IsGalois K L] in
theorem nu_R (w : Lˣ) : nu K L ((Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ) w) = 1 := by
  refine Units.ext ?_
  rw [Units.coe_map]
  change Algebra.norm K ((((Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ) w : Lˣ)) : L) = 1
  rw [coe_R_apply]
  have hw : Algebra.norm K (w : L) ≠ 0 := Algebra.norm_ne_zero_iff.mpr w.ne_zero
  have key : Algebra.norm K (σ (w : L) / (w : L)) * Algebra.norm K (w : L) = Algebra.norm K (w : L) := by
    rw [← map_mul, div_mul_cancel₀ _ w.ne_zero]
    exact Algebra.norm_eq_of_algEquiv σ (w : L)
  rcases mul_left_eq_self₀.mp key with h | h
  · exact h
  · exact absurd h hw

omit [IsGalois K L] in
theorem Rgrp_le_ker : Rgrp σ ≤ (nu K L).ker := by
  rintro x ⟨w, rfl⟩
  exact nu_R w

theorem mk_eq_mk_of_nu_eq (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {u u' : Lˣ}
    (h : nu K L u = nu K L u') : (QuotientGroup.mk u : Lˣ ⧸ Rgrp σ) = QuotientGroup.mk u' := by
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, hgen⟩⟩
  have h1 : Algebra.norm K (((u⁻¹ * u' : Lˣ)) : L) = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) (show nu K L (u⁻¹ * u') = 1 by rw [map_mul, map_inv, h, inv_mul_cancel])
    simpa only [Units.coe_map, MonoidHom.coe_coe, Units.val_one] using this
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one hgen h1
  refine QuotientGroup.eq.mpr ⟨y⁻¹, Units.ext ?_⟩
  rw [coe_R_apply, ← hy]
  have hy0 : (y : L) ≠ 0 := y.ne_zero
  have hσy0 : σ (y : L) ≠ 0 := by simp [hy0]
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  field_simp

theorem rel_iff_nu_mem_stab (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {γ₀ : GL (Fin 2) K} (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    {δ₀ : GL (Fin 2) L} {a₀ : Kˣ}
    (hδ₀ : normClassMap hgen (SigmaConjClasses.mk σ δ₀) = ConjClasses.mk (sc a₀ * γ₀)) (u : Lˣ) :
    (∃ h : GL (Fin 2) L, sc u * δ₀ = h⁻¹ * δ₀ * σ' h) ↔ nu K L u ∈ stab γ₀ := by
  have hsc : normClassMap hgen (SigmaConjClasses.mk σ (sc u * δ₀)) =
      ConjClasses.mk (sc (nu K L u * a₀) * γ₀) := by
    rw [normClassMap_scalar_mul hgen hδ₀ u, map_mul, mul_assoc]
  constructor
  · rintro hrel
    have hmk : SigmaConjClasses.mk σ δ₀ = SigmaConjClasses.mk σ (sc u * δ₀) :=
      SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr hrel
    have := hδ₀.symm.trans ((congrArg (normClassMap hgen) hmk).trans hsc)
    rw [mk_scalar_mul_eq_iff] at this
    simpa using this
  · intro hmem
    have hcl : ConjClasses.mk (sc a₀ * γ₀) = ConjClasses.mk (sc (nu K L u * a₀) * γ₀) := by
      rw [mk_scalar_mul_eq_iff]; simpa using hmem
    have h2 : normClassMap hgen (SigmaConjClasses.mk σ (sc u * δ₀)) = ConjClasses.mk (sc a₀ * γ₀) := by
      rw [hsc, ← hcl]
    have hmk := LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell hgen
      (sc a₀ * γ₀) (scalar_mul_mem_ellipticCell a₀ hγ₀) δ₀ (sc u * δ₀) hδ₀ h2
    exact SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mp hmk

theorem card_weight_eq (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {γ₀ : GL (Fin 2) K} (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    {δ₀ : GL (Fin 2) L} {a₀ : Kˣ}
    (hδ₀ : normClassMap hgen (SigmaConjClasses.mk σ δ₀) = ConjClasses.mk (sc a₀ * γ₀)) :
    Nat.card {q : Lˣ ⧸ Rgrp σ // ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
        sc u * δ₀ = h⁻¹ * δ₀ * σ' h} =
      Nat.card {a : Kˣ // a ∈ stab γ₀ ∧ a ∈ (nu K L).range} := by
  classical

  let nq : Lˣ ⧸ Rgrp σ →* Kˣ := QuotientGroup.lift (Rgrp σ) (nu K L) Rgrp_le_ker
  have hnq : ∀ u : Lˣ, nq (QuotientGroup.mk u) = nu K L u := fun u => rfl
  let e : {q : Lˣ ⧸ Rgrp σ // ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
      sc u * δ₀ = h⁻¹ * δ₀ * σ' h} → {a : Kˣ // a ∈ stab γ₀ ∧ a ∈ (nu K L).range} :=
    fun q => ⟨nq q.1, by
      obtain ⟨u, hu, hrel⟩ := q.2
      rw [← hu, hnq]
      exact ⟨(rel_iff_nu_mem_stab hgen hγ₀ hδ₀ u).mp hrel, ⟨u, rfl⟩⟩⟩
  refine Nat.card_congr (Equiv.ofBijective e ⟨?_, ?_⟩)
  · rintro ⟨q, u, rfl, hrel⟩ ⟨q', u', rfl, hrel'⟩ heq
    have : nu K L u = nu K L u' := by
      have := congrArg Subtype.val heq
      simpa [e, hnq] using this
    exact Subtype.ext (mk_eq_mk_of_nu_eq hgen this)
  · rintro ⟨a, ha, u, rfl⟩
    refine ⟨⟨QuotientGroup.mk u, u, rfl, (rel_iff_nu_mem_stab hgen hγ₀ hδ₀ u).mpr ha⟩, ?_⟩
    exact Subtype.ext (hnq u)

end Weights
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"

end LT.TwistedNorm.EllipticWeights
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"

namespace LT
p2m_export "LT" "mk TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.normClassMap TwistedNorm.IsNormClass"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell sigmaPartialNorm sigmaPartialNorm_succ' sigmaNormPow sigmaNormPow_def coe_sigmaNormPow_units_eq_algebraMap_norm SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map IsNormRep normRep isNormRep_normRep normClassMap normClassMap_mk normClassMap_mk_eq_of_isNormRep IsNormClass isNormClass_mk_iff"
namespace EllipticWeights
p2m_open "LT.TwistedNorm LT"

section Fibre

open Function

theorem finsum_comp_eq_card_smul_finsum {α β : Type*} (π : α → β) (hπ : Surjective π) (k : ℕ) (hk : k ≠ 0)
    (hfib : ∀ b : β, Nat.card (π ⁻¹' {b}) = k) (g : β → ℂ) :
    (∑ᶠ a, g (π a)) = (k : ℂ) * ∑ᶠ b, g b := by
  classical
  have hfibfin : ∀ b : β, (π ⁻¹' {b}).Finite := fun b =>
    Nat.finite_of_card_ne_zero (by rw [hfib b]; exact hk)
  by_cases hfin : (support g).Finite
  · have hA : (support (g ∘ π)).Finite := by
      rw [support_comp_eq_preimage]
      exact hfin.preimage' fun b _ => hfibfin b
    set sA := hA.toFinset with hsA
    set sB := hfin.toFinset with hsB
    have hgA : support (fun a => g (π a)) ⊆ sA := by
      intro a ha; rw [hsA, Finset.mem_coe, Set.Finite.mem_toFinset]; exact ha
    have hgB : support g ⊆ sB := by
      intro b hb; rw [hsB, Finset.mem_coe, Set.Finite.mem_toFinset]; exact hb
    rw [finsum_eq_sum_of_support_subset _ hgA, finsum_eq_sum_of_support_subset _ hgB, Finset.mul_sum]
    have hmaps : ∀ a ∈ sA, π a ∈ sB := by
      intro a ha
      rw [hsA, Set.Finite.mem_toFinset] at ha
      rw [hsB, Set.Finite.mem_toFinset]
      exact ha
    rw [← Finset.sum_fiberwise_of_maps_to' hmaps g]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hbsupp : b ∈ support g := by rwa [hsB, Set.Finite.mem_toFinset] at hb
    have hbsupp' : g b ≠ 0 := hbsupp
    have hset : (sA.filter fun a => π a = b) = (hfibfin b).toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, hsA,
        Function.mem_support, Function.comp_apply]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by rw [h]; exact hbsupp', h⟩
    rw [hset, ← Set.ncard_eq_toFinset_card _ (hfibfin b), ← Nat.card_coe_set_eq, hfib b]
  · have hB : ∑ᶠ b, g b = 0 := finsum_of_infinite_support hfin
    have hA : ¬ (support (g ∘ π)).Finite := by
      intro hA
      apply hfin
      rw [support_comp_eq_preimage] at hA
      have := hA.image π
      rwa [Set.image_preimage_eq _ hπ] at this
    rw [hB, mul_zero]
    exact finsum_of_infinite_support hA

end Fibre
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"

section Assembly

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ : L ≃ₐ[K] L}

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)
local notation "σ'" => Matrix.GeneralLinearGroup.map (σ : L →+* L)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conj_scalar_mul' (c : Lˣ) (g h k : GL (Fin 2) L) :
    h * (sc c * g) * k = sc c * (h * g * k) := by
  rw [show h * (sc c * g) * k = (h * sc c) * (g * k) by simp only [mul_assoc], ← scalar_mul_comm c h]
  simp only [mul_assoc]

theorem mk_eq_mk_scalar_of_mk_scalar_eq {F : Type*} [Field F] (a b : Fˣ) (g g' : GL (Fin 2) F)
    (h : ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) b * g')) :
    ConjClasses.mk g = ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) (a⁻¹ * b) * g') := by
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have e : c * (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g) * c⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a * (c * g * c⁻¹) := by
    simpa only [inv_inv] using conj_scalar_mul a g c⁻¹
  rw [e] at hc
  rw [map_mul, mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹), ← hc, ← mul_assoc, ← map_mul,
    inv_mul_cancel, map_one, one_mul]

theorem main (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    (RL : Set (GL (Fin 2) L))
    (hRL₁ : ∀ δ₁ ∈ RL, ∀ δ₂ ∈ RL, ∀ (h : GL (Fin 2) L) (u : Lˣ), δ₂ = sc u * (h⁻¹ * δ₁ * σ' h) → δ₁ = δ₂)
    (hRL₂ : ∀ (δ : GL (Fin 2) L) (a : Kˣ),
      normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (sc a * γ₀) →
      ∃ δ₀ ∈ RL, ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = sc u * (h⁻¹ * δ₀ * σ' h))
    (A : GL (Fin 2) L → Kˣ)
    (hA : ∀ δ₀ ∈ RL, (∃ a : Kˣ, normClassMap hgen (SigmaConjClasses.mk σ δ₀) = ConjClasses.mk (sc a * γ₀)) →
      normClassMap hgen (SigmaConjClasses.mk σ δ₀) = ConjClasses.mk (sc (A δ₀) * γ₀))
    (T : Set Kˣ)
    (hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b)
    (Φ : Kˣ → ℂ)
    (hΦS : ∀ a s : Kˣ, (∃ h : GL (Fin 2) K, sc s * γ₀ = h⁻¹ * γ₀ * h) → Φ (a * s) = Φ a)
    (hΦN : ∀ (a : Kˣ) (b : Lˣ), Φ (a * Units.map (Algebra.norm K : L →* K) b) = Φ a)
    (hΦ0 : ∀ a : Kˣ, ¬ IsNormClass hgen (ConjClasses.mk (sc a * γ₀)) → Φ a = 0) :
    (∑ᶠ δ₀ ∈ RL ∩ {δ | ∃ a : Kˣ,
        normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (sc a * γ₀)},
      ((Nat.card {q : Lˣ ⧸ Rgrp σ // ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            sc u * δ₀ = h⁻¹ * δ₀ * σ' h} : ℕ) : ℂ)⁻¹ * Φ (A δ₀)) =
      ∑ᶠ t ∈ T, ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K, sc a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ * Φ t := by
  classical

  set S : Subgroup Kˣ := stab γ₀ with hS
  set N : Subgroup Kˣ := (nu K L).range with hN
  set SN : Subgroup Kˣ := S ⊔ N with hSN
  haveI : N.Normal := inferInstance
  haveI : SN.Normal := inferInstance
  have hNSN : N ≤ SN := le_sup_right

  set m₀ : ℕ := Nat.card {a : Kˣ // a ∈ S ∧ a ∈ N} with hm₀
  set P : Set (GL (Fin 2) L) := {δ | ∃ a : Kˣ,
    normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (sc a * γ₀)} with hP
  have hAP : ∀ δ₀ ∈ RL ∩ P, normClassMap hgen (SigmaConjClasses.mk σ δ₀) = ConjClasses.mk (sc (A δ₀) * γ₀) :=
    fun δ₀ h => hA δ₀ h.1 h.2
  have hwt : ∀ δ₀ ∈ RL ∩ P, (Nat.card {q : Lˣ ⧸ Rgrp σ // ∃ u : Lˣ, QuotientGroup.mk u = q ∧
      ∃ h : GL (Fin 2) L, sc u * δ₀ = h⁻¹ * δ₀ * σ' h} : ℕ) = m₀ :=
    fun δ₀ h => card_weight_eq hgen hγ₀ (hAP δ₀ h)

  have hΦSN : ∀ (a : Kˣ) (x : Kˣ), x ∈ SN → Φ (a * x) = Φ a := by
    intro a x hx
    rw [hSN, Subgroup.mem_sup] at hx
    obtain ⟨s, hs, n, ⟨w, rfl⟩, rfl⟩ := hx
    rw [← mul_assoc, hΦN, hΦS a s hs]
  let Φ₂ : Kˣ ⧸ SN → ℂ := fun c => Φ c.out
  have hΦ₂ : ∀ a : Kˣ, Φ₂ (QuotientGroup.mk a) = Φ a := by
    intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul SN a
    show Φ (QuotientGroup.mk a : Kˣ ⧸ SN).out = Φ a
    rw [hx, hΦSN a x x.2]

  set Cn : Set (Kˣ ⧸ SN) := {c | ∃ b : Kˣ, QuotientGroup.mk b = c ∧
    IsNormClass hgen (ConjClasses.mk (sc b * γ₀))} with hCn
  have hbij : Set.BijOn (fun δ₀ => (QuotientGroup.mk (A δ₀) : Kˣ ⧸ SN)) (RL ∩ P) Cn := by
    refine ⟨?_, ?_, ?_⟩
    · intro δ₀ hδ₀
      exact ⟨A δ₀, rfl, ⟨SigmaConjClasses.mk σ δ₀, hAP δ₀ hδ₀⟩⟩
    · intro δ₁ hδ₁ δ₂ hδ₂ heq
      have h12 : (A δ₁)⁻¹ * A δ₂ ∈ SN := QuotientGroup.eq.mp heq
      rw [hSN, Subgroup.mem_sup] at h12
      obtain ⟨s, hs, n, ⟨w, rfl⟩, hsn⟩ := h12

      have hw : normClassMap hgen (SigmaConjClasses.mk σ (sc w * δ₁)) = ConjClasses.mk (sc (A δ₂) * γ₀) := by
        rw [normClassMap_scalar_mul hgen (hAP δ₁ hδ₁) w, ← mul_assoc, ← map_mul, mk_scalar_mul_eq_iff]
        have : (nu K L w * A δ₁)⁻¹ * A δ₂ = s := by
          rw [mul_inv_rev, mul_comm (A δ₁)⁻¹, mul_assoc, show (A δ₁)⁻¹ * A δ₂ = s * nu K L w from hsn.symm,
            mul_comm s, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [this]; exact hs
      have hmk := LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell hgen
        (sc (A δ₂) * γ₀) (scalar_mul_mem_ellipticCell (A δ₂) hγ₀) (sc w * δ₁) δ₂ hw (hAP δ₂ hδ₂)
      obtain ⟨h, hh⟩ := SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mp hmk
      rw [conj_scalar_mul'] at hh
      exact hRL₁ δ₁ hδ₁.1 δ₂ hδ₂.1 h w hh
    · intro c hc
      obtain ⟨b, rfl, hnc⟩ := hc
      obtain ⟨δ, hδ⟩ := (isNormClass_mk_iff hgen _).mp hnc
      have hncm : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (sc b * γ₀) :=
        normClassMap_mk_eq_of_isNormRep hgen hδ
      obtain ⟨δ₀, hδ₀RL, h, u, rfl⟩ := hRL₂ δ b hncm

      have h0 : normClassMap hgen (SigmaConjClasses.mk σ (h⁻¹ * δ₀ * σ' h)) =
          ConjClasses.mk (normRep hgen δ₀) := by
        rw [normClassMap_mk_sigmaConj, normClassMap_mk]
      have h1 : ConjClasses.mk (sc b * γ₀) = ConjClasses.mk (sc (nu K L u) * normRep hgen δ₀) := by
        rw [← hncm, normClassMap_scalar_mul hgen h0 u]
      have h2 : ConjClasses.mk (normRep hgen δ₀) = ConjClasses.mk (sc ((nu K L u)⁻¹ * b) * γ₀) := by
        have := mk_eq_mk_scalar_of_mk_scalar_eq (nu K L u) b (normRep hgen δ₀) γ₀ h1.symm
        exact this
      have hPδ₀ : δ₀ ∈ RL ∩ P := ⟨hδ₀RL, (nu K L u)⁻¹ * b, by rw [normClassMap_mk, h2]⟩
      refine ⟨δ₀, hPδ₀, ?_⟩

      have h3 := (hAP δ₀ hPδ₀).symm.trans (by rw [normClassMap_mk, h2] :
        normClassMap hgen (SigmaConjClasses.mk σ δ₀) = ConjClasses.mk (sc ((nu K L u)⁻¹ * b) * γ₀))
      rw [mk_scalar_mul_eq_iff] at h3
      show (QuotientGroup.mk (A δ₀) : Kˣ ⧸ SN) = QuotientGroup.mk b
      refine QuotientGroup.eq.mpr ?_
      rw [hSN, Subgroup.mem_sup]
      refine ⟨(A δ₀)⁻¹ * ((nu K L u)⁻¹ * b), h3, nu K L u, ⟨u, rfl⟩, ?_⟩
      rw [mul_assoc, inv_mul_cancel_comm]
  have hL : (∑ᶠ δ₀ ∈ RL ∩ P, ((Nat.card {q : Lˣ ⧸ Rgrp σ // ∃ u : Lˣ, QuotientGroup.mk u = q ∧
      ∃ h : GL (Fin 2) L, sc u * δ₀ = h⁻¹ * δ₀ * σ' h} : ℕ) : ℂ)⁻¹ * Φ (A δ₀)) =
      ∑ᶠ c ∈ Cn, (m₀ : ℂ)⁻¹ * Φ₂ c := by
    refine finsum_mem_eq_of_bijOn _ hbij fun δ₀ hδ₀ => ?_
    beta_reduce
    rw [hwt δ₀ hδ₀, hΦ₂]

  have hCn0 : ∀ c : Kˣ ⧸ SN, c ∉ Cn → Φ₂ c = 0 := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H b =>
      rw [hΦ₂]
      apply hΦ0
      intro hnc
      exact hc ⟨b, rfl, hnc⟩
  have hsupp2 : (Function.support fun c => (m₀ : ℂ)⁻¹ * Φ₂ c) ⊆ Cn := by
    intro c hc
    by_contra hcn
    exact hc (by simp only [hCn0 c hcn, mul_zero])
  have hL' : (∑ᶠ c ∈ Cn, (m₀ : ℂ)⁻¹ * Φ₂ c) = ∑ᶠ c, (m₀ : ℂ)⁻¹ * Φ₂ c := by
    calc (∑ᶠ c ∈ Cn, (m₀ : ℂ)⁻¹ * Φ₂ c)
        = ∑ᶠ c ∈ Cn ∩ Function.support (fun c => (m₀ : ℂ)⁻¹ * Φ₂ c), (m₀ : ℂ)⁻¹ * Φ₂ c :=
          (finsum_mem_inter_support _ _).symm
      _ = ∑ᶠ c ∈ Set.univ ∩ Function.support (fun c => (m₀ : ℂ)⁻¹ * Φ₂ c), (m₀ : ℂ)⁻¹ * Φ₂ c := by
          rw [Set.inter_eq_right.mpr hsupp2, Set.univ_inter]
      _ = ∑ᶠ c, (m₀ : ℂ)⁻¹ * Φ₂ c := by rw [finsum_mem_inter_support, finsum_mem_univ]

  let Φ₁ : Kˣ ⧸ N → ℂ := fun q => Φ₂ (QuotientGroup.map N SN (MonoidHom.id Kˣ) (by simpa using hNSN) q)
  have hΦ₁ : ∀ a : Kˣ, Φ₁ (QuotientGroup.mk a) = Φ a := by
    intro a
    show Φ₂ (QuotientGroup.map N SN (MonoidHom.id Kˣ) _ (QuotientGroup.mk a)) = Φ a
    rw [QuotientGroup.map_mk, MonoidHom.id_apply, hΦ₂]
  have hcardS : Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K, sc a * γ₀ = h⁻¹ * γ₀ * h} = Nat.card S := rfl
  have hbijT : Set.BijOn (fun t : Kˣ => (QuotientGroup.mk t : Kˣ ⧸ N)) T Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro t ht t' ht' heq
      have h1 : t⁻¹ * t' ∈ N := QuotientGroup.eq.mp heq
      obtain ⟨w, hw⟩ := h1
      have e1 : t' = t * nu K L w := by rw [hw, mul_inv_cancel_left]
      have e2 : t' = t' * nu K L 1 := by rw [map_one, mul_one]
      obtain ⟨t₀, -, huniq⟩ := hT t'
      have := (huniq t ⟨ht, w, e1⟩).trans (huniq t' ⟨ht', 1, e2⟩).symm
      exact this
    · intro q _
      induction q using QuotientGroup.induction_on with
      | H a =>
        obtain ⟨t, ⟨ht, b, hab⟩, -⟩ := hT a
        refine ⟨t, ht, ?_⟩
        show (QuotientGroup.mk t : Kˣ ⧸ N) = QuotientGroup.mk a
        exact QuotientGroup.eq.mpr ⟨b, by rw [hab, inv_mul_cancel_left]⟩
  have hR : (∑ᶠ t ∈ T, ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K, sc a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ * Φ t) =
      ∑ᶠ q, ((Nat.card S : ℕ) : ℂ)⁻¹ * Φ₁ q := by
    have key := finsum_mem_eq_of_bijOn (t := Set.univ) (g := fun q => ((Nat.card S : ℕ) : ℂ)⁻¹ * Φ₁ q)
      (f := fun t => ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K, sc a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ * Φ t)
      _ hbijT fun t _ => by beta_reduce; rw [hcardS, hΦ₁]
    rw [finsum_mem_univ] at key
    exact key

  set π : Kˣ ⧸ N →* Kˣ ⧸ SN := QuotientGroup.map N SN (MonoidHom.id Kˣ) (by simpa using hNSN) with hπ
  have hπsurj : Function.Surjective π := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H a => exact ⟨QuotientGroup.mk a, rfl⟩
  have hker : π.ker = S.map (QuotientGroup.mk' N) := by
    rw [hπ, QuotientGroup.ker_map, Subgroup.comap_id, hSN, Subgroup.map_sup]
    have : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨n, hn, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    rw [this, sup_bot_eq]
  set k : ℕ := Nat.card π.ker with hk
  have hfib : ∀ c : Kˣ ⧸ SN, Nat.card (π ⁻¹' {c}) = k := by
    intro c
    obtain ⟨q₀, rfl⟩ := hπsurj c
    refine Nat.card_congr (Equiv.ofBijective (fun x : π ⁻¹' {π q₀} => (⟨q₀⁻¹ * x.1, by
      have hx := x.2
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]⟩ : π.ker)) ⟨?_, ?_⟩)
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      have := congrArg Subtype.val h
      simp only at this
      exact Subtype.ext (mul_left_cancel this)
    · rintro ⟨y, hy⟩
      refine ⟨⟨q₀ * y, ?_⟩, Subtype.ext (by simp)⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff, map_mul, MonoidHom.mem_ker.mp hy, mul_one]

  have hcard : Nat.card S = k * m₀ := by
    let f : S →* Kˣ ⧸ N := (QuotientGroup.mk' N).domRestrict S
    have hrange : f.range = S.map (QuotientGroup.mk' N) := MonoidHom.domRestrict_range S (QuotientGroup.mk' N)
    have hkerf : f.ker = N.subgroupOf S := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.domRestrict_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
    have e1 : Nat.card S = Nat.card (S ⧸ f.ker) * Nat.card f.ker := Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have e2 : Nat.card (S ⧸ f.ker) = Nat.card f.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have e3 : Nat.card f.range = k := by rw [hrange, ← hker]
    have e4 : Nat.card f.ker = m₀ := by
      rw [hkerf, hm₀]
      refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, Subgroup.mem_subgroupOf.mp x.2⟩,
        fun a => ⟨⟨a.1, a.2.1⟩, Subgroup.mem_subgroupOf.mpr a.2.2⟩, fun x => rfl, fun a => rfl⟩
    rw [e1, e2, e3, e4]
  have hk0 : k ≠ 0 := by
    rw [hk]
    haveI : Finite π.ker := by
      rw [hker]
      exact Finite.of_surjective (fun s : S => ⟨QuotientGroup.mk' N s.1, s.1, s.2, rfl⟩)
        (by rintro ⟨x, s, hs, rfl⟩; exact ⟨⟨s, hs⟩, rfl⟩)
    exact Nat.card_pos.ne'
  have hm0 : m₀ ≠ 0 := by
    rw [hm₀]
    haveI : Finite {a : Kˣ // a ∈ S ∧ a ∈ N} :=
      Finite.of_injective (fun a => (⟨a.1, a.2.1⟩ : S)) (by rintro ⟨a, _⟩ ⟨b, _⟩ h; cases h; rfl)
    haveI : Nonempty {a : Kˣ // a ∈ S ∧ a ∈ N} := ⟨⟨1, S.one_mem, N.one_mem⟩⟩
    exact Nat.card_pos.ne'

  have hfibsum : (∑ᶠ q, ((Nat.card S : ℕ) : ℂ)⁻¹ * Φ₁ q) = (k : ℂ) * ∑ᶠ c, ((Nat.card S : ℕ) : ℂ)⁻¹ * Φ₂ c :=
    finsum_comp_eq_card_smul_finsum π hπsurj k hk0 hfib (fun c => ((Nat.card S : ℕ) : ℂ)⁻¹ * Φ₂ c)
  rw [show RL ∩ {δ | ∃ a : Kˣ, normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (sc a * γ₀)} = RL ∩ P
    from rfl, hL, hL', hR, hfibsum]

  have hkS : (k : ℂ) * ((Nat.card S : ℕ) : ℂ)⁻¹ = (m₀ : ℂ)⁻¹ := by
    rw [hcard, Nat.cast_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk0), one_mul]
  rw [mul_finsum]
  exact finsum_congr fun c => by rw [← mul_assoc, hkS]

end Assembly
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"

end LT.TwistedNorm.EllipticWeights
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"
p2m_reactivate "P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.LT.TwistedNorm.EllipticWeights"

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    (RL : Set (GL (Fin 2) L))
    (hRL₁ : ∀ δ₁ ∈ RL, ∀ δ₂ ∈ RL, ∀ (h : GL (Fin 2) L) (u : Lˣ),
      δ₂ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        (h⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) → δ₁ = δ₂)
    (hRL₂ : ∀ (δ : GL (Fin 2) L) (a : Kˣ),
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
        ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) →
      ∃ δ₀ ∈ RL, ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h))
    (A : GL (Fin 2) L → Kˣ)
    (hA : ∀ δ₀ ∈ RL, (∃ a : Kˣ,
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₀) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₀) =
        ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) (A δ₀) * γ₀))
    (T : Set Kˣ)
    (hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b)
    (Φ : Kˣ → ℂ)
    (hΦS : ∀ a s : Kˣ, (∃ h : GL (Fin 2) K,
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * γ₀ = h⁻¹ * γ₀ * h) → Φ (a * s) = Φ a)
    (hΦN : ∀ (a : Kˣ) (b : Lˣ), Φ (a * Units.map (Algebra.norm K : L →* K) b) = Φ a)
    (hΦ0 : ∀ a : Kˣ, ¬ LT.TwistedNorm.IsNormClass hgen
        (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) → Φ a = 0) :
    (∑ᶠ δ₀ ∈ RL ∩ {δ | ∃ a : Kˣ,
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)},
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} : ℕ) : ℂ)⁻¹ * Φ (A δ₀)) =
      ∑ᶠ t ∈ T,
        ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
            Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ * Φ t :=
  LT.TwistedNorm.EllipticWeights.main hgen γ₀ hγ₀ RL hRL₁ hRL₂ A hA T hT Φ hΦS hΦN hΦ0

end S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell
end P2MW
export P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell (solution)
