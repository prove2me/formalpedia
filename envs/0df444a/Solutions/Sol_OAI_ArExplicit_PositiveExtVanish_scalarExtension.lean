-- Prove2me | solution 1 for OAI.ArExplicit.PositiveExtVanish.scalarExtension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T15:30:30.388111+00:00
-- url     : https://prove2.me/submissions/17737314-ac87-4110-a969-759241b6998e

import Mathlib
import Definitions.Def_OAIQ031A059
import Definitions.Def_OAIQ031A060

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionProjective
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

attribute [local instance] scalarExtensionModule

variable (M : Type w) [AddCommGroup M] [Module R M] [Module k M]
  [IsScalarTower k R M]

theorem scalarExtension_projective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (E ⊗[k] R) (E ⊗[k] M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f (LinearMap.id : M →ₗ[R] M) hf
  let e := scalarExtensionPi k E R n
  let i := e.toLinearMap.comp (scalarExtensionMap k E R s)
  let p := (scalarExtensionMap k E R f).comp e.symm.toLinearMap
  apply Module.Projective.of_split i p
  ext x
  change scalarExtensionMap k E R f
    (e.symm (e (scalarExtensionMap k E R s x))) = x
  rw [e.symm_apply_apply]
  change ((scalarExtensionMap k E R f).comp (scalarExtensionMap k E R s)) x = x
  rw [← scalarExtensionMap_comp, hs, scalarExtensionMap_id]
  rfl

end ArExplicit

end

end OAI
end

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
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionHomExact
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
  {K L M N : Type w}
  [AddCommGroup K] [Module R K] [Module k K] [IsScalarTower k R K]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

attribute [local instance] scalarExtensionModule

theorem scalarExtensionHom_exact
    [Module.Finite R K] [Module.Projective R K]
    [Module.Finite R L] [Module.Projective R L]
    [Module.Finite R M] [Module.Projective R M]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M)
    (hex : Function.Exact (LinearMap.lcomp k N d) (LinearMap.lcomp k N e)) :
    Function.Exact
      (LinearMap.lcomp E (E ⊗[k] N) (scalarExtensionMap k E R d))
      (LinearMap.lcomp E (E ⊗[k] N) (scalarExtensionMap k E R e)) := by
  have hbase := Module.Flat.lTensor_exact E hex
  intro f
  constructor
  · intro hf
    obtain ⟨x, hx⟩ := (scalarExtensionHom_bijective k E R (M := L) (N := N)).2 f
    have hz : (LinearMap.lcomp k N e).lTensor E x = 0 := by
      apply (scalarExtensionHom_bijective k E R (M := K) (N := N)).1
      change scalarExtensionHom k E R ((LinearMap.lcomp k N e).baseChange E x) = _
      rw [scalarExtensionHom_precomp, hx, map_zero]
      exact hf
    obtain ⟨y, hy⟩ := (hbase x).1 hz
    refine ⟨scalarExtensionHom k E R y, ?_⟩
    change (scalarExtensionHom k E R y).comp (scalarExtensionMap k E R d) = f
    rw [← scalarExtensionHom_precomp]
    exact (congrArg (scalarExtensionHom k E R) hy).trans hx
  · rintro ⟨g, rfl⟩
    obtain ⟨y, rfl⟩ := (scalarExtensionHom_bijective k E R (M := M) (N := N)).2 g
    change ((scalarExtensionHom k E R y).comp (scalarExtensionMap k E R d)).comp
      (scalarExtensionMap k E R e) = 0
    rw [← scalarExtensionHom_precomp, ← scalarExtensionHom_precomp]
    change scalarExtensionHom k E R
      ((LinearMap.lcomp k N e).lTensor E ((LinearMap.lcomp k N d).lTensor E y)) = 0
    rw [(hbase _).2 ⟨y, rfl⟩, map_zero]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionComplete
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]

attribute [local instance] moduleCatBaseModule

attribute [local instance] moduleCatBaseTower scalarExtensionModule

theorem scalarExtensionComplex_exact (P : ChainComplex (ModuleCat.{w} R) ℤ)
    (h : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom) (n : ℤ) :
    LinearMap.range ((scalarExtensionComplex k E R P).d (n + 1) n).hom =
      LinearMap.ker ((scalarExtensionComplex k E R P).d n (n - 1)).hom :=
  (LinearMap.exact_iff.mp (scalarExtensionMap_exact k E R _ _
    (LinearMap.exact_iff.mpr (h n).symm))).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  (M N : Type w)
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower scalarExtensionModule

theorem PositiveExtVanish.scalarExtension_oai
    (hgp : GorensteinProjective R M) (h : PositiveExtVanish R M N) :
    PositiveExtVanish (E ⊗[k] R) (E ⊗[k] M) (E ⊗[k] N) := by
  obtain ⟨P, hp, he, hd, ⟨e⟩⟩ := hgp
  let (i : ℤ) : Module.Finite R (P.X i) := (hp i).1
  let (i : ℤ) : Module.Projective R (P.X i) := (hp i).2
  let PE := scalarExtensionComplex k E R P
  have hpE (i : ℤ) : Module.Projective (E ⊗[k] R) (PE.X i) :=
    scalarExtension_projective k E R (P.X i)
  have heE (i : ℤ) : LinearMap.range (PE.d (i + 1) i).hom =
      LinearMap.ker (PE.d i (i - 1)).hom :=
    scalarExtensionComplex_exact k E R P he i
  let eE : (E ⊗[k] M) ≃ₗ[E ⊗[k] R] CompleteCokernel PE :=
    (scalarExtensionEquiv k E R e).trans
      (scalarExtensionCokernelEquiv k E R (P.d 1 0).hom).symm
  apply (positiveExtVanish_iff_completeResolution (E ⊗[k] R) (E ⊗[k] M)
    (E ⊗[k] N) PE hpE heE eE).2
  have hbase := (positiveExtVanish_iff_completeResolution R M N P
    (fun i => (hp i).2) he e).1 h
  intro n f hf
  have hex : Function.Exact
      (LinearMap.lcomp k N (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom)
      (LinearMap.lcomp k N (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom) := by
    intro f
    constructor
    · intro hf
      obtain ⟨g, hg⟩ := hbase n f hf
      exact ⟨g, hg.symm⟩
    · rintro ⟨g, rfl⟩
      change (g.comp (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom).comp
        (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom = 0
      rw [LinearMap.comp_assoc, show
        (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom.comp
          (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom = 0 from
          congrArg ModuleCat.Hom.hom (P.d_comp_d _ _ _), LinearMap.comp_zero]
  have hE := scalarExtensionHom_exact k E R
    (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom
    (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom hex
  obtain ⟨g, hg⟩ := (hE f).1 hf
  exact ⟨g, hg.symm⟩

end ArExplicit

end

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.ArExplicit.PositiveExtVanish.scalarExtension_oai.{u, v, w} := @OAI.ArExplicit.PositiveExtVanish.scalarExtension_oai.{u, v, w}
