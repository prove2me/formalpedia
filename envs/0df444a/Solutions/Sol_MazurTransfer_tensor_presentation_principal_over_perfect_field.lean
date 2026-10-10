-- Prove2me | solution 1 for MazurTransfer.tensor_presentation_principal_over_perfect_field
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T23:16:28.231732+00:00
-- url     : https://prove2.me/submissions/521ab6fe-e317-49b7-9346-8071694acd8d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete required tensor helper proofs reused from official Anthropic FLT
at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: tensor products give addition of actual divisor classes
over a perfect field with its full constant-field property explicit.
Named downstream consumer: the unchanged actual order-13 arithmetic Picard
group correspondence. Original public theorem statements are unchanged.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve WithZero TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
universe u
namespace MazurTransfer.PublicTensorPresentationHelpers
variable {X : Scheme.{u}}
noncomputable abbrev rM (M : X.Modules) {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y
variable [IsIntegral X]
theorem nonempty_inf (U W : X.Opens) [hU : Nonempty U] [hW : Nonempty W] : Nonempty (U ⊓ W : X.Opens) := by
  obtain ⟨⟨u, hu⟩⟩ := hU
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨u, hu⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

omit [IsIntegral X] in
theorem IsFrameOn.ne_zero_of_nontrivial {M : X.Modules} {U : X.Opens} [Nontrivial Γ(X, U)] {s : Γ(M, U)}
    (hs : IsFrameOn s U) : s ≠ 0 := by
  intro h
  have h1 : (1 : Γ(X, U)) • M.presheaf.map (homOfLE (le_refl U)).op s = 0 := by
    rw [h, map_zero, smul_zero]
  have := (hs.smul_eq_zero_iff le_rfl le_rfl (1 : Γ(X, U))).mp h1
  exact one_ne_zero this

variable {L L' : X.Modules}

theorem exists_forall_tensorSections_eq_mul
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V (L'.presheaf.map (homOfLE h).op m) = φ' U m)
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U)) :
    ∃ f : X.functionField, f ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (s : Γ(L, U)) (t : Γ(L', U)),
      φ'' U (tensorSections s t) = f * φ U s * φ' U t := by
  classical

  obtain ⟨U₁, s₁, hη₁, hs₁⟩ := hL.exists_isFrameOn (genericPoint X)
  obtain ⟨U₂, t₂, hη₂, ht₂⟩ := hL'.exists_isFrameOn (genericPoint X)
  let V : X.Opens := U₁ ⊓ U₂
  haveI : Nonempty V := ⟨⟨genericPoint X, hη₁, hη₂⟩⟩
  let s₀ : Γ(L, V) := rM L inf_le_left s₁
  let t₀ : Γ(L', V) := rM L' inf_le_right t₂
  have hs₀ : IsFrameOn s₀ V := (hs₁.map (homOfLE (inf_le_left : V ≤ U₁))).mono inf_le_left
  have ht₀ : IsFrameOn t₀ V := (ht₂.map (homOfLE (inf_le_right : V ≤ U₂))).mono inf_le_right
  have hst₀ : IsFrameOn (tensorSections s₀ t₀) V := hs₀.tensorSections ht₀
  have hφs : φ V s₀ ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial hs₀ (hinj V inferInstance (by rw [h, map_zero]))
  have hφt : φ' V t₀ ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial ht₀ (hinj' V inferInstance (by rw [h, map_zero]))
  have hφst : φ'' V (tensorSections s₀ t₀) ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial hst₀ (hinj'' V inferInstance (by rw [h, map_zero]))
  refine ⟨φ'' V (tensorSections s₀ t₀) / (φ V s₀ * φ' V t₀), div_ne_zero hφst (mul_ne_zero hφs hφt), ?_⟩
  intro U hU s t
  let W : X.Opens := U ⊓ V
  haveI : Nonempty W := nonempty_inf U V

  obtain ⟨a, ha⟩ := (hs₀ (inf_le_right : W ≤ V) inf_le_right).2 (rM L (inf_le_left : W ≤ U) s)
  obtain ⟨b, hb⟩ := (ht₀ (inf_le_right : W ≤ V) inf_le_right).2 (rM L' (inf_le_left : W ≤ U) t)
  simp only at ha hb

  have e1 : φ'' U (tensorSections s t) = algebraMap Γ(X, W) X.functionField (a * b) * φ'' V (tensorSections s₀ t₀) := by
    rw [← hnat'' U W inf_le_left inferInstance (tensorSections s t), map_homOfLE_tensorSections]
    change φ'' W (tensorSections (rM L (inf_le_left : W ≤ U) s) (rM L' (inf_le_left : W ≤ U) t)) = _
    rw [← ha, ← hb, tensorSections_smul_left, tensorSections_smul_right, ← mul_smul,
      ← map_homOfLE_tensorSections, hsmul'', hnat'' V W inf_le_right inferInstance]
  have e2 : φ U s = algebraMap Γ(X, W) X.functionField a * φ V s₀ := by
    rw [← hnat U W inf_le_left inferInstance s]
    change φ W (rM L (inf_le_left : W ≤ U) s) = _
    rw [← ha, hsmul, hnat V W inf_le_right inferInstance]
  have e3 : φ' U t = algebraMap Γ(X, W) X.functionField b * φ' V t₀ := by
    rw [← hnat' U W inf_le_left inferInstance t]
    change φ' W (rM L' (inf_le_left : W ≤ U) t) = _
    rw [← hb, hsmul', hnat' V W inf_le_right inferInstance]
  rw [e1, e2, e3, map_mul]
  field_simp
  try ring

end MazurTransfer.PublicTensorPresentationHelpers
open MazurTransfer.PublicTensorPresentationHelpers

theorem solution
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (L L' : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (D D' D'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V ((L).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V ((L').presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U))
    (hrange'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ'' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D'' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D'' - D - D') := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra

  obtain ⟨E, ψ, e1, e2, e3, e4, e5⟩ := Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x L hL
  obtain ⟨E', ψ', e1', e2', e3', e4', e5'⟩ := Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x L' hL'
  obtain ⟨E'', ψ'', e1'', e2'', e3'', e4'', e5''⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x (L ⊗ L') (hL.tensor hL')

  obtain ⟨f, hf0, hf⟩ := exists_forall_tensorSections_eq_mul hL hL' ψ ψ' ψ'' e1 e1' e1'' e2 e2' e2'' e3 e3' e3''

  have hpt : ∀ v : Place K X.functionField, (E'' - E - E') v = v.ord f⁻¹ := by
    intro v
    obtain ⟨y, hy, hv⟩ := exists_closedPoint_range_stalk_eq x v

    obtain ⟨U₁, s₁, hy₁, hs₁⟩ := hL.exists_isFrameOn y
    obtain ⟨U₂, t₂, hy₂, ht₂⟩ := hL'.exists_isFrameOn y
    let W : X.Opens := U₁ ⊓ U₂
    have hyW : y ∈ W := ⟨hy₁, hy₂⟩
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    let s : Γ(L, W) := rM L inf_le_left s₁
    let t : Γ(L', W) := rM L' inf_le_right t₂
    have hs : IsFrameOn s W := (hs₁.map (homOfLE (inf_le_left : W ≤ U₁))).mono inf_le_left
    have ht : IsFrameOn t W := (ht₂.map (homOfLE (inf_le_right : W ≤ U₂))).mono inf_le_right
    have hst : IsFrameOn (tensorSections s t) W := hs.tensorSections ht

    have gen : ∀ {M : X.Modules} (m : Γ(M, W)), IsFrameOn m W →
        ∀ (W' : X.Opens) (h : W' ≤ W), y ∈ W' → ∀ m' : Γ(M, W'), ∃ a : Γ(X, W'),
          m' = a • M.presheaf.map (homOfLE h).op m := by
      intro M m hm W' h _ m'
      obtain ⟨a, ha⟩ := (hm h h).2 m'
      exact ⟨a, ha.symm⟩
    have k := e5 W s y hyW hy (gen s hs) v hv
    have k' := e5' W t y hyW hy (gen t ht) v hv
    have k'' := e5'' W (tensorSections s t) y hyW hy (gen _ hst) v hv
    rw [hf W s t, Valuation.map_mul, Valuation.map_mul, ← k, ← k'] at k''

    have hfv : v.adicValuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf0
    have hfv' : v.adicValuation f = exp (-(v.ord f)) := by
      simp only [Place.ord, neg_neg, WithZero.exp_log hfv]
    rw [hfv', ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_injective.eq_iff] at k''
    simp only [Finsupp.coe_sub, Pi.sub_apply, Place.ord_inv]
    linarith
  have hP0 : Divisor.IsPrincipal (E'' - E - E') := ⟨f⁻¹, inv_ne_zero hf0, hpt⟩

  have hsec : ∀ {M : X.Modules}, Scheme.Modules.IsInvertible M → ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0 := by
    intro M hM
    obtain ⟨U, s, hη, hs⟩ := hM.exists_isFrameOn (genericPoint X)
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    exact ⟨U, s, IsFrameOn.ne_zero_of_nontrivial hs⟩

  obtain ⟨-, -, -, -, hP1⟩ := MazurTransfer.presentation_ratio_principal_over_perfect_field x hC L D E φ ψ
    hnat e1 hsmul e2 hinj e3 hrange e4 (hsec hL)
  obtain ⟨-, -, -, -, hP2⟩ := MazurTransfer.presentation_ratio_principal_over_perfect_field x hC L' D' E' φ' ψ'
    hnat' e1' hsmul' e2' hinj' e3' hrange' e4' (hsec hL')
  obtain ⟨-, -, -, -, hP3⟩ := MazurTransfer.presentation_ratio_principal_over_perfect_field x hC (L ⊗ L') D'' E''
    φ'' ψ'' hnat'' e1'' hsmul'' e2'' hinj'' e3'' hrange'' e4'' (hsec (hL.tensor hL'))

  have key : D'' - D - D' = (D'' - E'') - (D - E) - (D' - E') + (E'' - E - E') := by abel
  rw [key]
  have mem : (D'' - E'') - (D - E) - (D' - E') + (E'' - E - E') ∈ Divisor.principal (K := K) (F := X.functionField) :=
    add_mem (sub_mem (sub_mem hP3 hP1) hP2) hP0
  exact mem

#print axioms solution
