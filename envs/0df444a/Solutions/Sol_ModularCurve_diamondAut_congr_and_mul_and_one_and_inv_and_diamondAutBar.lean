-- Prove2me | solution 1 for ModularCurve.diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ebea81d4-6895-5347-b3d5-3ba394706a20

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_xHFunctionField_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve IntermediateField

namespace DiamAutLaws

section BaseChange

variable {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

theorem isBaseChangeAutOf_unique {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    {σ σ' : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀}
    (h : IsBaseChangeAutOf L σ₀ σ) (h' : IsBaseChangeAutOf L σ₀ σ') : σ = σ' := by
  apply AlgEquiv.ext
  rintro ⟨x, hx⟩
  have hx' : x ∈ IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      apply Subtype.ext
      exact (h ⟨z, hz⟩).trans (h' ⟨z, hz⟩).symm
  | algebraMap c =>
      have : (⟨algebraMap L (LaurentSeries L) c, IntermediateField.algebraMap_mem _ c⟩ :
          laurentBaseChange L F₀) = algebraMap L (laurentBaseChange L F₀) c := rfl
      rw [this, AlgEquiv.commutes, AlgEquiv.commutes]
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz]

variable (L) [Algebra.IsAlgebraic ℚ L]

theorem baseChangeAut_eq_geomAut (σ₀ : F₀ ≃ₐ[ℚ] F₀) :
    baseChangeAut L σ₀ = geomAut L F₀ σ₀ := by
  have hgeom : IsBaseChangeAutOf L σ₀ (geomAut L F₀ σ₀) := fun y =>
    coe_geomAut_coeffEmb L F₀ σ₀ y
  exact isBaseChangeAutOf_unique (isBaseChangeAutOf_baseChangeAut ⟨_, hgeom⟩) hgeom

theorem diamondAutBar_eq_geomAut (N d : ℕ) :
    diamondAutBar N d = geomAut (AlgebraicClosure ℚ) (x1FunctionField N) (diamondAut N d) :=
  baseChangeAut_eq_geomAut (AlgebraicClosure ℚ) (diamondAut N d)

end BaseChange

theorem isDiamondAut_congr {N d d' : ℕ} (hd : d.Coprime N) (hd' : d'.Coprime N)
    (h : (d : ZMod N) = (d' : ZMod N)) : IsDiamondAut N d = IsDiamondAut N d' := by
  funext σ
  unfold IsDiamondAut
  rw [h]
  exact propext ⟨fun hx => ⟨hd', hx.2⟩, fun hx => ⟨hd, hx.2⟩⟩

theorem dite_exists_choose_congr {α : Sort*} {P P' : α → Prop} (e : P = P')
    {i : Decidable (∃ x, P x)} {i' : Decidable (∃ x, P' x)} (a : α) :
    @dite α (∃ x, P x) i (fun hP => hP.choose) (fun _ => a) =
      @dite α (∃ x, P' x) i' (fun hP => hP.choose) (fun _ => a) := by
  subst e
  have hi : i = i' := Subsingleton.elim _ _
  subst hi
  rfl

theorem diamondAut_congr {N d d' : ℕ} (hd : d.Coprime N) (hd' : d'.Coprime N)
    (h : (d : ZMod N) = (d' : ZMod N)) : diamondAut N d = diamondAut N d' := by
  unfold diamondAut
  exact dite_exists_choose_congr (isDiamondAut_congr hd hd' h) _

end DiamAutLaws

end

open ModularCurve in
theorem solution
    (N : ℕ) [NeZero N] :

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) = (d' : ZMod N)) →
      ModularCurve.diamondAut N d = ModularCurve.diamondAut N d') ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N →
      ∀ x : ↥(ModularCurve.x1FunctionField N),
        ModularCurve.diamondAut N (d * d') x = ModularCurve.diamondAut N d (ModularCurve.diamondAut N d' x)) ∧

    ModularCurve.diamondAut N 1 = AlgEquiv.refl ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) * (d' : ZMod N) = 1) →
      ∀ x : ↥(ModularCurve.x1FunctionField N),
        ModularCurve.diamondAut N d (ModularCurve.diamondAut N d' x) = x) ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) = (d' : ZMod N)) →
      ModularCurve.diamondAutBar N d = ModularCurve.diamondAutBar N d') ∧
    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N →
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar N),
        ModularCurve.diamondAutBar N (d * d') x = ModularCurve.diamondAutBar N d (ModularCurve.diamondAutBar N d' x)) ∧
    ModularCurve.diamondAutBar N 1 = AlgEquiv.refl ∧
    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) * (d' : ZMod N) = 1) →
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar N),
        ModularCurve.diamondAutBar N d (ModularCurve.diamondAutBar N d' x) = x) := by
  classical

  obtain ⟨δ, hδ, -⟩ := ModularCurve.exists_monoidHom_diamondAut_mem_xHFunctionField_iff N ⊤
    (fun d hd => ModularCurve.exists_isDiamondAut N hd)

  have hU : ∀ (d : ℕ) (hd : d.Coprime N),
      diamondAut N d = δ ⟨ZMod.unitOfCoprime d hd, Subgroup.mem_top _⟩ := by
    intro d hd
    rw [hδ]
    refine DiamAutLaws.diamondAut_congr hd (ZMod.val_coe_unit_coprime (ZMod.unitOfCoprime d hd)) ?_
    show (d : ZMod N) = (((ZMod.unitOfCoprime d hd : (ZMod N)ˣ) : ZMod N).val : ZMod N)
    rw [ZMod.natCast_zmod_val, ZMod.coe_unitOfCoprime]

  have hUmul : ∀ (d d' : ℕ) (hd : d.Coprime N) (hd' : d'.Coprime N),
      (⟨ZMod.unitOfCoprime (d * d') (Nat.Coprime.mul hd hd'), Subgroup.mem_top _⟩ : (⊤ : Subgroup (ZMod N)ˣ)) =
        ⟨ZMod.unitOfCoprime d hd, Subgroup.mem_top _⟩ * ⟨ZMod.unitOfCoprime d' hd', Subgroup.mem_top _⟩ := by
    intro d d' hd hd'
    apply Subtype.ext; apply Units.ext
    simp [ZMod.coe_unitOfCoprime, Nat.cast_mul]
  have hUone : (⟨ZMod.unitOfCoprime 1 (Nat.coprime_one_left N), Subgroup.mem_top _⟩ : (⊤ : Subgroup (ZMod N)ˣ)) = 1 := by
    apply Subtype.ext; apply Units.ext
    simp [ZMod.coe_unitOfCoprime]

  have hmulQ : ∀ (d d' : ℕ), d.Coprime N → d'.Coprime N →
      diamondAut N (d * d') = diamondAut N d * diamondAut N d' := by
    intro d d' hd hd'
    rw [hU d hd, hU d' hd', hU (d * d') (Nat.Coprime.mul hd hd'), hUmul d d' hd hd', map_mul]
  have honeQ : diamondAut N 1 = AlgEquiv.refl := by
    rw [hU 1 (Nat.coprime_one_left N), hUone, map_one]; rfl
  have hinvQ : ∀ (d d' : ℕ), d.Coprime N → d'.Coprime N → ((d : ZMod N) * (d' : ZMod N) = 1) →
      diamondAut N d * diamondAut N d' = AlgEquiv.refl := by
    intro d d' hd hd' h1
    rw [← hmulQ d d' hd hd', ← honeQ]
    exact DiamAutLaws.diamondAut_congr (Nat.Coprime.mul hd hd') (Nat.coprime_one_left N) (by rw [Nat.cast_mul, h1, Nat.cast_one])

  have hbar : ∀ d : ℕ, diamondAutBar N d = geomAut (AlgebraicClosure ℚ) (x1FunctionField N) (diamondAut N d) :=
    DiamAutLaws.diamondAutBar_eq_geomAut N
  refine ⟨fun d d' hd hd' h => DiamAutLaws.diamondAut_congr hd hd' h,
    fun d d' hd hd' x => by rw [hmulQ d d' hd hd', AlgEquiv.mul_apply],
    honeQ,
    fun d d' hd hd' h1 x => by rw [← AlgEquiv.mul_apply, hinvQ d d' hd hd' h1]; rfl,
    fun d d' hd hd' h => by rw [hbar, hbar, DiamAutLaws.diamondAut_congr hd hd' h],
    fun d d' hd hd' x => by rw [hbar, hbar, hbar, hmulQ d d' hd hd', map_mul, AlgEquiv.mul_apply],
    by rw [hbar, honeQ]; exact map_one (geomAut (AlgebraicClosure ℚ) (x1FunctionField N)),
    fun d d' hd hd' h1 x => by rw [hbar, hbar, ← AlgEquiv.mul_apply, ← map_mul, hinvQ d d' hd hd' h1]; exact congrArg (fun e : ↥(x1FunctionFieldBar N) ≃ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar N) => e x) (map_one (geomAut (AlgebraicClosure ℚ) (x1FunctionField N)))⟩

end S_ModularCurve_diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar
end P2MW
export P2MW.S_ModularCurve_diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar (solution)
