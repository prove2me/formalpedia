-- Prove2me | solution 1 for ModularCurve.finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/424bfe26-ddb4-5368-a870-4091e56901b5

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups IntermediateField

namespace A7BetaGeneric

open Cardinal IntermediateField

section Exchange

variable {L E : Type*} [Field L] [Field E] [Algebra L E]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem isAlgebraic_algebraAdjoin {x : E} [Algebra.IsAlgebraic L⟮x⟯ E] :
    Algebra.IsAlgebraic (Algebra.adjoin L ({x} : Set E)) E :=
  Algebra.IsAlgebraic.trans (Algebra.adjoin L ({x} : Set E)) L⟮x⟯ E

theorem isAlgebraic_adjoin_of_transcendental {x : E} (hx : Transcendental L x)
    [Algebra.IsAlgebraic L⟮x⟯ E] {y : E} (hy : Transcendental L y) :
    Algebra.IsAlgebraic L⟮y⟯ E := by
  have indx : AlgebraicIndependent L (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have indy : AlgebraicIndependent L (fun _ : Unit => y) :=
    algebraicIndependent_unique_type_iff.mpr hy
  have hrx : Set.range (fun _ : Unit => x) = {x} := Set.range_const
  have hry : Set.range (fun _ : Unit => y) = {y} := Set.range_const
  have algx : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range fun _ : Unit => x)) E := by
    rw [hrx]
    exact isAlgebraic_algebraAdjoin
  have basx : IsTranscendenceBasis L (fun _ : Unit => x) :=
    indx.isTranscendenceBasis_iff_isAlgebraic.mpr algx
  have basy : IsTranscendenceBasis L (fun _ : Unit => y) :=
    indy.isTranscendenceBasis_of_lift_trdeg_le_of_finite (le_of_eq basx.lift_cardinalMk_eq_trdeg.symm)
  have h := basy.isAlgebraic_field
  rwa [hry] at h

theorem finiteDimensional_adjoin_of_transcendental {x : E} (hx : Transcendental L x)
    [FiniteDimensional L⟮x⟯ E] {y : E} (hy : Transcendental L y) :
    FiniteDimensional L⟮y⟯ E := by
  haveI : Algebra.IsAlgebraic L⟮y⟯ E := isAlgebraic_adjoin_of_transcendental hx hy
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite L⟮x⟯ E)
  set S : Set E := insert x (↑s : Set E) with hS
  haveI : Finite S := (s.finite_toSet.insert x).to_subtype
  set K' : IntermediateField L⟮y⟯ E := IntermediateField.adjoin L⟮y⟯ S with hK'def
  haveI hK'fin : FiniteDimensional L⟮y⟯ K' :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

  have hxK' : x ∈ K' := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hLx_le : ∀ c : L⟮x⟯, (c : E) ∈ K' := by
    intro c
    have hle : L⟮x⟯ ≤ K'.restrictScalars L := IntermediateField.adjoin_simple_le_iff.mpr hxK'
    exact hle c.2

  have hK' : K' = ⊤ := by
    suffices h : ∀ e : E, e ∈ K' from eq_top_iff.mpr fun e _ => h e
    intro e
    have he : e ∈ Submodule.span L⟮x⟯ (↑s : Set E) := by rw [hs]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hz)
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul c z _ hz =>
        rw [IntermediateField.smul_def, smul_eq_mul] at *
        show (c : E) * z ∈ K'
        exact mul_mem (hLx_le c) hz
  have htop : FiniteDimensional L⟮y⟯ (⊤ : IntermediateField L⟮y⟯ E) := by
    rw [← hK']; exact hK'fin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := L⟮y⟯) (E := E)).toLinearEquiv

end Exchange

section Along

variable {L F F' : Type*} [Field L] [Field F] [Field F'] [Algebra L F] [Algebra L F']

theorem finiteAlong_of_transcendental (φ : F →ₐ[L] F') {x₀ : F} (hx₀ : Transcendental L x₀)
    {x₁ : F'} (hx₁ : Transcendental L x₁) [FiniteDimensional L⟮x₁⟯ F'] :
    AlgebraicCurve.FiniteAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ

  have hy₀ : Transcendental L (φ x₀) := by
    have h := (transcendental_algebraMap_iff (R := L) (S := F) (A := F')
      (φ.toRingHom.injective)).mpr hx₀
    exact h
  haveI hfin : FiniteDimensional L⟮φ x₀⟯ F' := finiteDimensional_adjoin_of_transcendental hx₁ hy₀

  set E₀ : IntermediateField L F := L⟮x₀⟯ with hE₀
  have hmap : E₀.map φ = L⟮φ x₀⟯ := by
    rw [hE₀, IntermediateField.adjoin_map, Set.image_singleton]
  let e : E₀ ≃ₐ[L] L⟮φ x₀⟯ := (E₀.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ w : E₀, ((e w : L⟮φ x₀⟯) : F') = φ (w : F) := by
    intro w
    rfl
  letI : Algebra E₀ F' := ((algebraMap F F').comp (algebraMap E₀ F)).toAlgebra
  haveI : IsScalarTower E₀ F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E₀ F' := by
    refine Module.Finite.of_equiv_equiv (A₁ := L⟮φ x₀⟯) (B₁ := F') (A₂ := E₀) (B₂ := F')
      e.symm.toRingEquiv (RingEquiv.refl F') ?_
    refine RingHom.ext fun z => ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.refl_apply]
    rw [show e.symm.toRingEquiv (e w) = w from e.symm_apply_apply w]
    show φ (w : F) = ((e w : L⟮φ x₀⟯) : F')
    rw [he]
  show Module.Finite F F'
  exact Module.Finite.of_restrictScalars_finite E₀ F F'

theorem isIntegral_of_finiteAlong (φ : F →ₐ[L] F') (h : AlgebraicCurve.FiniteAlong L φ) :
    φ.toRingHom.IsIntegral := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Module.Finite F F' := h
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  exact fun x => Algebra.IsIntegral.isIntegral x

theorem separableAlong_of_charZero [CharZero F] (φ : F →ₐ[L] F')
    (hφ : φ.toRingHom.IsIntegral) : AlgebraicCurve.SeparableAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Algebra.IsIntegral F F' := ⟨fun x => hφ x⟩
  show Algebra.IsSeparable F F'
  infer_instance

end Along

end A7BetaGeneric

namespace A7Beta

open ModularCurve AlgebraicCurve CongruenceSubgroup IntermediateField

variable (L : Type*) [Field L] [Algebra ℚ L] (M ℓ : ℕ)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_mem_Gamma1_inf_Gamma0 : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (M * ℓ) := by
  refine ⟨T_mem_Gamma1 M, ?_⟩
  simp [Gamma0_mem, ModularGroup.T]

variable [NeZero M] [NeZero ℓ]

scoped instance finiteIndex_Gamma1_inf_Gamma0 : (Gamma1 M ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  infer_instance

theorem exists_transcendental_bot :
    ∃ x₀ : laurentBaseChange L (x1FunctionField M), Transcendental L x₀ := by
  obtain ⟨x, hx, -⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L (Gamma1 M)
      (T_mem_Gamma1 M)
  exact ⟨x, hx⟩

theorem exists_transcendental_finiteDimensional_top :
    ∃ x₁ : laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)), Transcendental L x₁ ∧
      FiniteDimensional L⟮x₁⟯ (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
    (Gamma1 M ⊓ Gamma0 (M * ℓ)) (T_mem_Gamma1_inf_Gamma0 M ℓ)

theorem finiteAlong_any (φ : laurentBaseChange L (x1FunctionField M) →ₐ[L]
    laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : FiniteAlong L φ := by
  obtain ⟨x₀, hx₀⟩ := exists_transcendental_bot L M
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_top L M ℓ
  haveI := hfin
  exact A7BetaGeneric.finiteAlong_of_transcendental _ hx₀ hx₁

end A7Beta
p2m_reactivate "P2MW.S_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined.A7Beta"

end
p2m_reactivate "P2MW.S_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined.A7Beta"

theorem solution (L : Type*) [Field L]
    [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ]
    (h : ModularCurve.HeckeBetaOneDefined N ℓ) :
    AlgebraicCurve.FiniteAlong L (ModularCurve.heckeBetaOneBar L N ℓ) :=
  A7Beta.finiteAlong_any L N ℓ _

end S_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined
end P2MW
export P2MW.S_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined (solution)
