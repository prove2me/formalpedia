-- Prove2me | solution 1 for OAI.ArExplicit.Statement.fullStatement_of_mainConclusions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T15:32:42.479828+00:00
-- url     : https://prove2.me/submissions/c6a8aac5-e069-4d8a-af38-e670729a69e9

import Mathlib
import Definitions.Def_AuslanderReiten
import Definitions.Def_OAIQ031A076
import Theorems.Thm_OAI_ArExplicit_GorensteinProjective_scalarExtension
import Theorems.Thm_OAI_ArExplicit_PositiveExtVanish_scalarExtension
import Theorems.Thm_OAI_ArExplicit_nonprojective_scalarExtension

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_Radical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable {R S : Type*} [Ring R] [Ring S]

theorem map_mem_ideal_pow (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hf : ∀ x ∈ I, f x ∈ J) (n : ℕ) {x : R} (hx : x ∈ I ^ n) : f x ∈ J ^ n := by
  induction n generalizing x with
  | zero => simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ n hn =>
      rw [Submodule.pow_succ] at hx ⊢
      exact Submodule.mul_induction_on hx
        (fun a ha b hb => by rw [map_mul]; exact Ideal.mul_mem_mul (hn ha) (hf b hb))
        (fun a b ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)

theorem radical_pow_ne_bot_of_injective (f : R →+* S) (hf : Function.Injective f)
    (hJ : ∀ x ∈ Ring.jacobson R, f x ∈ Ring.jacobson S) (n : ℕ)
    (hn : (Ring.jacobson R) ^ n ≠ ⊥) : (Ring.jacobson S) ^ n ≠ ⊥ := by
  intro hs
  apply hn
  apply le_antisymm _ bot_le
  intro x hx
  have hmem := map_mem_ideal_pow f _ _ hJ n hx
  rw [hs] at hmem
  apply hf
  simpa only [Ideal.mem_bot, map_zero] using hmem

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (E : Type*) [Field E] [Algebra k E]

theorem scalarExtension_radical_pow_ne_bot (n : ℕ) (hn : (Ring.jacobson R) ^ n ≠ ⊥) :
    (Ring.jacobson (E ⊗[k] R)) ^ n ≠ ⊥ := by
  let f : R →+* E ⊗[k] R :=
    (Algebra.TensorProduct.includeRight : R →ₐ[k] E ⊗[k] R).toRingHom
  apply radical_pow_ne_bot_of_injective f
    (Algebra.TensorProduct.includeRight_injective (algebraMap k E).injective) _ n hn
  intro x hx
  apply nilpotentIdeal_le_jacobson
    (rightTensorIdeal (k := k) (R := E) (Ring.jacobson R))
    (rightTensorIdeal_isNilpotent _ (finiteAlgebra_radical_isNilpotent (k := k)))
  exact tmul_mem_rightTensorIdeal _ 1 hx

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_MainScalarExtension
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open scoped TensorProduct

universe u v

variable {k R M : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (E : Type (max u v)) [Field E] [Algebra k E]

attribute [local instance] scalarExtensionModule

theorem MainConclusions.scalarExtension (h : MainConclusions k R M) :
    MainConclusions E (E ⊗[k] R) (E ⊗[k] M) := by
  obtain ⟨hR, hM, hn, hgp, hself, _, ⟨e⟩, hrad⟩ := h
  let := hR
  let := hM
  let : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  have hgpE := hgp.scalarExtension k E R M
  let f : R →ₐ[k] (Fin 8 → k) := e.toAlgHom.comp (Ideal.Quotient.mkₐ k (Ring.jacobson R))
  have hf : Function.Surjective f := e.surjective.comp (Ideal.Quotient.mk_surjective)
  have hJ : Ring.jacobson R = RingHom.ker f := by
    ext x
    change x ∈ Ring.jacobson R ↔ e (Ideal.Quotient.mk (Ring.jacobson R) x) = 0
    rw [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨inferInstance, inferInstance, nonprojective_scalarExtension k E R hn,
    hgpE, hself.scalarExtension k E R M M hgp, hgpE.positiveExt_regular,
    ⟨scalarExtension_semisimpleQuotientEquiv E f hf hJ⟩,
    scalarExtension_radical_pow_ne_bot E 4 hrad⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolutionAllProjectives
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u v w x y
variable {R : Type u} [Ring R]
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {L : Type w} [AddCommGroup L] [Module R L]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable {Q : Type y} [AddCommGroup Q] [Module R Q]

theorem HomExactAt.arbitrary_projective [Module.Finite R L] [Module.Projective R Q]
    {e : K →ₗ[R] L} {d : L →ₗ[R] M} (h : HomExactAt e d)
    (f : L →ₗ[R] Q) (hf : f.comp e = 0) :
    ∃ g : M →ₗ[R] Q, g.comp d = f := by
  classical
  obtain ⟨s,hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R Q)
  obtain ⟨c,hc⟩ := (LinearMap.finsuppLinearMap_bijective_of_moduleFinite
    R L R Q ℤ).surjective (s.comp f)
  have he (q : Q) : (c q).comp e = 0 := by
    ext z
    have hh := congrArg (fun F : L →ₗ[R] (Q →₀ R) => F (e z) q) hc
    change (c q) (e z) = (s (f (e z))) q at hh
    rw [show f (e z) = 0 from DFunLike.congr_fun hf z, map_zero] at hh
    exact hh
  choose g hg using fun q => h (c q) (he q)
  let G : M →ₗ[R] (Q →₀ R) := ∑ q ∈ c.support, (Finsupp.lsingle q).comp (g q)
  have hG : G.comp d = s.comp f := by
    ext z q
    have hh := congrArg (fun F : L →ₗ[R] (Q →₀ R) => F z q) hc
    change (c q) z = (s (f z)) q at hh
    change G (d z) q = (s (f z)) q
    rw [← hh]
    change (∑ j ∈ c.support, (Finsupp.lsingle j).comp (g j)) (d z) q = (c q) z
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Finsupp.finsetSum_apply]
    have hg' (j : Q) : g j (d z) = (c j) z := DFunLike.congr_fun (hg j) z
    simp only [hg', Finsupp.lsingle_apply]
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hq
      have hcz : c q = 0 := Finsupp.notMem_support_iff.mp hq
      simp [hcz]
  refine ⟨(Finsupp.linearCombination R id).comp G, ?_⟩
  rw [LinearMap.comp_assoc, hG, ← LinearMap.comp_assoc, hs, LinearMap.id_comp]

theorem GorensteinProjective.all_projective_targets
    {M : Type v} [AddCommGroup M] [Module R M]
    (h : GorensteinProjective R M) : GorensteinProjectiveAllTargets.{u,v,y} R M := by
  obtain ⟨P,hP,he,hd,hi⟩ := h
  refine ⟨P,hP,he,?_,hi⟩
  intro Q _ _ _ n f hf
  let := (hP n).1
  have hn : HomExactAt (P.d (n+1) n).hom (P.d n (n-1)).hom := by
    intro f hf
    obtain ⟨g,hg⟩ := hd n f hf
    exact ⟨g,hg.symm⟩
  obtain ⟨g,hg⟩ := hn.arbitrary_projective f hf
  exact ⟨g,hg.symm⟩

theorem gorensteinProjective_iff_all_projective_targets
    {M : Type v} [AddCommGroup M] [Module R M] :
    GorensteinProjective R M ↔ GorensteinProjectiveAllTargets.{u,v,u} R M := by
  refine ⟨GorensteinProjective.all_projective_targets, ?_⟩
  rintro ⟨P,hP,he,hd,hi⟩
  exact ⟨P,hP,he,hd R,hi⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_StatementEquivalence
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.Statement
universe u v

theorem conclusions_iff {F R Z : Type u} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup Z] [Module R Z] [Module F Z] [IsScalarTower F R Z] :
    ArExplicit.MainConclusions F R Z ↔ Conclusions F R Z := by
  constructor
  · rintro ⟨hR,hZ,hn,hg,hs,hr,hq,h4⟩
    exact ⟨hR,hZ,hn,hg.all_projective_targets,hs,hr,hq,h4⟩
  · rintro ⟨hR,hZ,hn,hg,hs,hr,hq,h4⟩
    exact ⟨hR,hZ,hn,ArExplicit.gorensteinProjective_iff_all_projective_targets.mpr hg,
      hs,hr,hq,h4⟩

theorem fullStatement_of_mainConclusions_oai (c : ArExplicit.Candidate)
    (h : ArExplicit.MainConclusions ArExplicit.BaseField c.R c.M) : FullStatement.{v} := by
  let s : System :=
    { algebraCarrier := c.R
      ring := c.ring
      scalarAlgebra := c.algebra
      moduleCarrier := c.M
      additiveGroup := c.addCommGroup
      action := c.module
      scalarAction := c.baseModule
      actionTower := c.tower }
  refine ⟨ArExplicit.parameters_algebraicallyIndependent,s,conclusions_iff.mp h,?_⟩
  intro E _ _
  let := ArExplicit.scalarExtensionModule K E c.R c.M
  refine ⟨ArExplicit.scalarExtensionModule K E c.R c.M,
    ArExplicit.scalarExtensionIsScalarTower K E c.R c.M,?_,?_⟩
  · intro a b r z
    exact ArExplicit.scalarExtension_smul_tmul K E c.R c.M a b r z
  · exact conclusions_iff.mp (h.scalarExtension E)

end ArExplicit.Statement

end

end OAI
end

theorem solution.{v} : type_of% @OAI.ArExplicit.Statement.fullStatement_of_mainConclusions_oai.{v} := @OAI.ArExplicit.Statement.fullStatement_of_mainConclusions_oai.{v}
