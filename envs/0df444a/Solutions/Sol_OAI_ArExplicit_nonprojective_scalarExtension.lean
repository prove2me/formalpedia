-- Prove2me | solution 1 for OAI.ArExplicit.nonprojective_scalarExtension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T15:31:36.86918+00:00
-- url     : https://prove2.me/submissions/05b55508-eac0-4378-bb25-1aea9f2f1b29

import Mathlib
import Definitions.Def_OAIQ031A060

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

theorem scalarExtensionHom_bijective_pi (n : ℕ) :
    Function.Bijective (scalarExtensionHom k E R (M := Fin n → R) (N := N)) := by
  let s : (E ⊗[k] ((Fin n → R) →ₗ[R] N)) ≃ₗ[E] (Fin n → E ⊗[k] N) :=
    ((LinearEquiv.piRing R N (Fin n) k).baseChange k E).trans
      (TensorProduct.piRight k E E (fun _ : Fin n => N))
  let t := scalarExtensionHomCoordinates k E R (N := N) n
  have heq : t.toLinearMap.comp (scalarExtensionHom k E R) = s.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul e f =>
      funext i
      change (scalarExtensionHom k E R (e ⊗ₜ[k] f))
        ((scalarExtensionPi k E R n).symm (Pi.single i 1)) = e ⊗ₜ[k] f (Pi.single i 1)
      have hi : (scalarExtensionPi k E R n).symm (Pi.single i 1) =
          (1 : E) ⊗ₜ[k] (Pi.single i (1 : R)) := by
        change (TensorProduct.piRight k E E (fun _ : Fin n => R)).symm
          (Pi.single i ((1 : E) ⊗ₜ[k] (1 : R))) = _
        exact TensorProduct.piRight_symm_single k E E _ 1 i 1
      rw [hi, scalarExtensionHom_tmul]
      simp only [LinearMap.smul_apply, scalarExtensionMap_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have heq_apply (x) : t (scalarExtensionHom k E R x) = s x :=
    LinearMap.congr_fun heq x
  constructor
  · intro x y h
    apply s.injective
    rw [← heq_apply, ← heq_apply, h]
  · intro f
    obtain ⟨x, hx⟩ := s.surjective (t f)
    exact ⟨x, t.injective ((heq_apply x).trans hx)⟩

theorem scalarExtensionHom_precomp (f : M →ₗ[R] N) (x : E ⊗[k] (N →ₗ[R] L)) :
    scalarExtensionHom k E R ((LinearMap.lcomp k L f).baseChange E x) =
      (scalarExtensionHom k E R x).comp (scalarExtensionMap k E R f) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]
  | tmul e g =>
    simp only [LinearMap.baseChange_tmul, LinearMap.lcomp_apply',
      scalarExtensionHom_tmul, scalarExtensionMap_comp, LinearMap.smul_comp]

theorem scalarExtensionHom_bijective [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (scalarExtensionHom k E R (M := M) (N := N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  let a := (LinearMap.lcomp k N p).baseChange E
  let b := (LinearMap.lcomp k N s).baseChange E
  have hba (x : E ⊗[k] (M →ₗ[R] N)) : b (a x) = x := by
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul e f =>
      change e ⊗ₜ[k] (f.comp p).comp s = e ⊗ₜ[k] f
      rw [LinearMap.comp_assoc, hs, LinearMap.comp_id]
  have hfree := scalarExtensionHom_bijective_pi k E R (N := N) n
  constructor
  · intro x y h
    have hxy : a x = a y := hfree.1 (by
      simp only [a, scalarExtensionHom_precomp, h])
    exact (hba x).symm.trans ((congrArg b hxy).trans (hba y))
  · intro f
    obtain ⟨x, hx⟩ := hfree.2 (f.comp (scalarExtensionMap k E R p))
    refine ⟨b x, ?_⟩
    rw [show b = (LinearMap.lcomp k N s).baseChange E from rfl,
      scalarExtensionHom_precomp, hx, LinearMap.comp_assoc,
      ← scalarExtensionMap_comp, hs, scalarExtensionMap_id, LinearMap.comp_id]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionPresentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {P Q M N : Type w}
  [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]
  [AddCommGroup Q] [Module R Q] [Module k Q] [IsScalarTower k R Q]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

attribute [local instance] scalarExtensionModule

omit [Module k P] [IsScalarTower k R P] [Module k Q] [IsScalarTower k R Q]
  [Module k M] [IsScalarTower k R M] in

theorem moduleHom_exact (d : Q →ₗ[R] P) (p : P →ₗ[R] M)
    (hex : Function.Exact d p) (hp : Function.Surjective p) :
    Function.Exact (LinearMap.lcomp k N p) (LinearMap.lcomp k N d) := by
  intro f
  simp only [LinearMap.lcomp_apply', Set.mem_range]
  constructor
  · intro hf
    refine ⟨((LinearMap.range d).liftQ f (LinearMap.range_le_ker_iff.mpr hf)).comp
      (hex.linearEquivOfSurjective hp).symm.toLinearMap, ?_⟩
    ext x
    simp
  · rintro ⟨g, rfl⟩
    rw [LinearMap.comp_assoc, hex.linearMap_comp_eq_zero, LinearMap.comp_zero]

theorem scalarExtensionHom_bijective_of_presentation
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q]
    (d : Q →ₗ[R] P) (p : P →ₗ[R] M)
    (hex : Function.Exact d p) (hp : Function.Surjective p) :
    Function.Bijective (scalarExtensionHom k E R (M := M) (N := N)) := by
  have hi : Function.Injective (LinearMap.lcomp k N p) :=
    LinearMap.lcomp_injective_of_surjective p hp
  have hbi := Module.Flat.lTensor_preserves_injective_linearMap (M := E) (LinearMap.lcomp k N p) hi
  have he := Module.Flat.lTensor_exact E (moduleHom_exact k R d p hex hp (N := N))
  have hpE := scalarExtensionMap_surjective k E R p hp
  have hiE : Function.Injective
      (LinearMap.lcomp E (E ⊗[k] N) (scalarExtensionMap k E R p)) :=
    LinearMap.lcomp_injective_of_surjective _ hpE
  constructor
  · intro x y hxy
    apply hbi
    apply (scalarExtensionHom_bijective k E R (M := P) (N := N)).1
    change scalarExtensionHom k E R ((LinearMap.lcomp k N p).baseChange E x) =
      scalarExtensionHom k E R ((LinearMap.lcomp k N p).baseChange E y)
    simp only [scalarExtensionHom_precomp, hxy]
  · intro f
    obtain ⟨x, hx⟩ := (scalarExtensionHom_bijective k E R (M := P) (N := N)).2
      (f.comp (scalarExtensionMap k E R p))
    have hz : (LinearMap.lcomp k N d).lTensor E x = 0 := by
      apply (scalarExtensionHom_bijective k E R (M := Q) (N := N)).1
      change scalarExtensionHom k E R ((LinearMap.lcomp k N d).baseChange E x) = _
      rw [scalarExtensionHom_precomp, hx, LinearMap.comp_assoc,
        ← scalarExtensionMap_comp, hex.linearMap_comp_eq_zero, map_zero]
      ext x
      simp [scalarExtensionMap]
    obtain ⟨y, hy⟩ := (he x).1 hz
    refine ⟨y, hiE ?_⟩
    change (scalarExtensionHom k E R y).comp (scalarExtensionMap k E R p) =
      f.comp (scalarExtensionMap k E R p)
    rw [← scalarExtensionHom_precomp]
    exact (congrArg (scalarExtensionHom k E R) hy).trans hx

theorem scalarExtensionHom_bijective_finite [Module.Finite k R] [Module.Finite R M] :
    Function.Bijective (scalarExtensionHom k E R (M := M) (N := N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let : Module.Finite k (LinearMap.ker p) :=
    Module.Finite.of_injective ((LinearMap.ker p).subtype.restrictScalars k)
      (LinearMap.ker p).injective_subtype
  let : Module.Finite R (LinearMap.ker p) :=
    Module.Finite.of_restrictScalars_finite k R _
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' R (LinearMap.ker p)
  let d := (LinearMap.ker p).subtype.comp q
  have hex : Function.Exact d p := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hq ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, rfl⟩
      exact (q y).property
  exact scalarExtensionHom_bijective_of_presentation k E R d p hex hp

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionDescent
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]

theorem exists_preimage_of_baseChange {V W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (w : W)
    (h : ∃ x : E ⊗[k] V, f.baseChange E x = (1 : E) ⊗ₜ[k] w) :
    ∃ v : V, f v = w := by
  obtain ⟨x, hx⟩ := h
  let q := (LinearMap.range f).mkQ
  have hq : q.comp f = 0 := LinearMap.range_mkQ_comp f
  have hz : (1 : E) ⊗ₜ[k] q w = 0 := by
    change q.baseChange E ((1 : E) ⊗ₜ[k] w) = 0
    rw [← hx]
    change ((q.baseChange E).comp (f.baseChange E)) x = 0
    rw [← LinearMap.baseChange_comp, hq, LinearMap.baseChange_zero]
    rfl
  have hqw : q w = 0 := by
    apply Module.Flat.tensorProduct_mk_injective (R := k) (S := E)
      (M := W ⧸ LinearMap.range f)
    simpa using hz
  have hw : w ∈ LinearMap.ker q := hqw
  change w ∈ LinearMap.ker (LinearMap.range f).mkQ at hw
  rw [Submodule.ker_mkQ] at hw
  exact hw

variable (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

theorem scalarExtensionHom_postcomp (f : N →ₗ[R] L) (x : E ⊗[k] (M →ₗ[R] N)) :
    scalarExtensionHom k E R ((moduleHomPostcomp k R f).baseChange E x) =
      (scalarExtensionMap k E R f).comp (scalarExtensionHom k E R x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]
  | tmul e g =>
    simp only [LinearMap.baseChange_tmul, scalarExtensionHom_tmul]
    change e • scalarExtensionMap k E R (f.comp g) =
      (scalarExtensionMap k E R f).comp (e • scalarExtensionMap k E R g)
    rw [scalarExtensionMap_comp]
    ext z
    exact ((scalarExtensionMap k E R f).restrictScalars E).map_smul e
      (scalarExtensionMap k E R g z) |>.symm

theorem projective_of_scalarExtension [Module.Finite k R] [Module.Finite R M]
    [Module.Projective (E ⊗[k] R) (E ⊗[k] M)] : Module.Projective R M := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨sE, hsE⟩ := Module.projective_lifting_property
    (scalarExtensionMap k E R p) (LinearMap.id : (E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] M))
    (scalarExtensionMap_surjective k E R p hp)
  obtain ⟨x, hx⟩ := (scalarExtensionHom_bijective_finite k E R
    (M := M) (N := Fin n → R)).2 sE
  have heq : (moduleHomPostcomp k R p).baseChange E x =
      (1 : E) ⊗ₜ[k] (LinearMap.id : M →ₗ[R] M) := by
    apply (scalarExtensionHom_bijective_finite k E R (M := M) (N := M)).1
    rw [scalarExtensionHom_postcomp, hx, hsE, scalarExtensionHom_tmul,
      scalarExtensionMap_id, one_smul]
  obtain ⟨s, hs⟩ := exists_preimage_of_baseChange k E (moduleHomPostcomp k R p)
    (LinearMap.id : M →ₗ[R] M) ⟨x, heq⟩
  change p.comp s = LinearMap.id at hs
  exact Module.Projective.of_split s p hs

theorem nonprojective_scalarExtension_oai [Module.Finite k R] [Module.Finite R M]
    (h : ¬ Module.Projective R M) :
    ¬ Module.Projective (E ⊗[k] R) (E ⊗[k] M) := by
  intro hE
  let := hE
  exact h (projective_of_scalarExtension k E R)

end ArExplicit

end

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.ArExplicit.nonprojective_scalarExtension_oai.{u, v, w} := @OAI.ArExplicit.nonprojective_scalarExtension_oai.{u, v, w}
