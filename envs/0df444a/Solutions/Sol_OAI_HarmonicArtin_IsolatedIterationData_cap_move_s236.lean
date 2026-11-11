-- Prove2me | solution 1 for OAI.HarmonicArtin.IsolatedIterationData.cap_move_s236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T20:14:40.072827+00:00
-- url     : https://prove2.me/submissions/d691f82e-c764-4f77-9c9d-2b31c7f47e8c

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap013
import Theorems.Thm_OAI_HarmonicArtin_fusionOrbitColor_subobject_separation_s236

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_BlockClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] in
lemma block_inclusion_projection (E:BasedComplex Q (K:=K) I) (T:Set I) :
    blockInclusion Q E T*blockProjection Q E T=projectiveIdentity Q (fun i:T=>E.placement i) := by
  rw [blockInclusion_mul Q E T _ _ (blockProjection_entries Q E T)]
  apply Matrix.ext
  intro i j
  change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
    (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
  simp only [Subtype.val_inj]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

namespace BasedComplex

variable [Fintype I] [Fintype J]

lemma homDifferential_square_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    homDifferential Q E F (n + 1) (homDifferential Q E F n f) = 0 := by
  change E.differential * (E.differential * f - cochainSign n • (f * F.differential)) -
    cochainSign (n + 1) • ((E.differential * f - cochainSign n • (f * F.differential)) *
      F.differential) = 0
  have h₁ : E.differential * (E.differential * f) = 0 := by
    rw [← Matrix.mul_assoc, E.square_zero, Matrix.zero_mul]
  have h₂ : (f * F.differential) * F.differential = 0 := by
    rw [Matrix.mul_assoc, F.square_zero, Matrix.mul_zero]
  rw [cochainSign_add_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    h₁, h₂, neg_smul, smul_zero, sub_zero, zero_sub, Matrix.mul_assoc]
  abel

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

namespace BasedComplex
variable [Fintype I] [Fintype J]

omit [Fintype V] in
lemma homBoundaries_le_homCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homBoundaries Q E F n v ≤ homCycles Q E F n v := by
  rintro _ ⟨f, hf, rfl⟩
  constructor
  · change homDifferential Q E F (n - 1) f ∈ homSpace Q E F n v
    have hd := homDifferential_mem Q E F (n - 1) v hf
    rw [sub_add_cancel] at hd
    exact hd
  · change homDifferential Q E F n (homDifferential Q E F (n - 1) f) = 0
    simpa only [sub_add_cancel] using homDifferential_square_zero Q E F (n - 1) f

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpaceDuality
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

attribute [local instance] OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.zigzagFiniteDimensional
lemma homSpace_finrank_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    Module.finrank K (homSpace Q F E (-n) (2-v)) = Module.finrank K (homSpace Q E F n v) :=
  (homSpaceDuality Q E F n v).finrank_eq.trans Subspace.dual_finrank_eq

omit [DecidableEq A] in

lemma homDifferential_adjoint (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) (g : Matrix J I (Q.Zigzag K)) :
    supertrace Q E (homDifferential Q E F (n-1) f * g) =
      cochainSign (K := K) n * supertrace Q E (f * homDifferential Q F E (-n) g) := by
  have hcyc := supertrace_mul Q E E E.degree (f*g)
  have hs := cochainSign_mul_self (K := K) n
  have hn : cochainSign (K := K) (n-1) = -cochainSign n := by
    have hh := cochainSign_add_one (K := K) (n-1)
    rw [sub_add_cancel] at hh
    linear_combination hh
  change supertrace Q E ((E.differential*f - cochainSign (K := K) (n-1) • (f*F.differential))*g) =
    cochainSign (K := K) n * supertrace Q E (f*(F.differential*g - cochainSign (K := K) (-n) • (g*E.differential)))
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    map_sub, map_sub, map_smul, map_smul]
  change supertrace Q E (E.differential*f*g) - cochainSign (K := K) (n-1) *
    supertrace Q E (f*F.differential*g) = cochainSign (K := K) n *
    (supertrace Q E (f*(F.differential*g)) - cochainSign (K := K) (-n) *
    supertrace Q E (f*(g*E.differential)))
  rw [cochainSign_neg, hn, Matrix.mul_assoc f F.differential g,
    Matrix.mul_assoc E.differential f g]
  have h1 : cochainSign (K := K) 1 = -1 := by
    simpa only [zero_add, cochainSign_zero] using cochainSign_add_one (K := K) 0
  rw [h1, neg_one_mul, Matrix.mul_assoc] at hcyc
  have hh : supertrace Q E (E.differential*(f*g)) = -supertrace Q E (f*(g*E.differential)) := by
    linear_combination hcyc
  rw [hh]
  linear_combination (supertrace Q E (f*(g*E.differential))) * hs

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_LinearMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

namespace BasedComplex

lemma cochainSign_ne_zero (n : ℤ) : cochainSign (K := K) n ≠ 0 := by
  intro h
  have hh := cochainSign_mul_self (K := K) n
  rw [h, MulZeroClass.zero_mul] at hh
  exact zero_ne_one hh

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
lemma homStep_range (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    (LinearMap.range (homStep Q E F n m v hm)).map (homSpace Q E F m v).subtype =
      homBoundaries Q E F m v := by
  subst m
  ext f
  change (∃ g, (∃ h, homStep Q E F n (n+1) v rfl h = g) ∧ g.val = f) ↔ _
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    change ∃ g, g ∈ homSpace Q E F (n+1-1) v ∧
      homDifferential Q E F (n+1-1) g = homDifferential Q E F n h.val
    simpa only [add_sub_cancel_right] using
      (show ∃ g, g ∈ homSpace Q E F n v ∧ homDifferential Q E F n g =
        homDifferential Q E F n h.val from ⟨h.val, h.property, rfl⟩)
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ homSpace Q E F n v := by
      change g ∈ homSpace Q E F (n+1-1) v at hg
      rwa [add_sub_cancel_right] at hg
    refine ⟨homStep Q E F n (n+1) v rfl ⟨g, hg'⟩, ⟨⟨g, hg'⟩, rfl⟩, ?_⟩
    dsimp only [homStep, LinearMap.restrict_apply]
    simp only [add_sub_cancel_right]

omit [Fintype V] [DecidableEq A] in
lemma homStep_range_finrank (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    Module.finrank K (LinearMap.range (homStep Q E F n m v hm)) =
      Module.finrank K (homBoundaries Q E F m v) := by
  rw [← homStep_range Q E F n m v hm, Submodule.finrank_map_subtype_eq]

omit [DecidableEq A] in

lemma hom_exact_dimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v + Module.finrank K (homBoundaries Q E F n v) +
      Module.finrank K (homBoundaries Q E F (n+1) v) =
      Module.finrank K (homSpace Q E F n v) := by
  have hq := ((homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype).finrank_quotient_add_finrank
  have hc := (Submodule.comapSubtypeEquivOfLe (homBoundaries_le_homCycles Q E F n v)).finrank_eq
  have hk := (homCycleKernelEquiv Q E F n (n+1) v rfl).finrank_eq
  have hr := homStep_range_finrank Q E F n (n+1) v rfl
  have he := (homStep Q E F n (n+1) v rfl).finrank_range_add_finrank_ker
  change homDimension Q E F n v + _ = _ at hq
  omega

lemma homStep_rank_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    Module.finrank K (homBoundaries Q E F m v) =
      Module.finrank K (homBoundaries Q F E (-n) (2-v)) := by
  have hneg : -n = -m+1 := by omega
  let d := homStep Q E F n m v hm
  let d' := homStep Q F E (-m) (-n) (2-v) hneg
  let e₀ := homSpaceDuality Q E F m v
  let e₁ := (homSpaceDuality Q E F n v).trans
    (LinearEquiv.smulOfNeZero K (Module.Dual K (homSpace Q E F n v))
      (cochainSign (K := K) m) (cochainSign_ne_zero m))
  have ha : e₁.toLinearMap.comp d' = d.dualMap.comp e₀.toLinearMap := by
    ext g f
    change cochainSign (K := K) m *
      supertrace Q E (f.val * homDifferential Q F E (-m) g.val) =
      supertrace Q E (homDifferential Q E F n f.val * g.val)
    have hh := homDifferential_adjoint Q E F m f.val g.val
    have he : m-1=n := by omega
    rw [he] at hh
    exact hh.symm
  have hr := congrArg (fun l : homSpace Q F E (-m) (2-v) →ₗ[K] Module.Dual K (homSpace Q E F n v) =>
    Module.finrank K (LinearMap.range l)) ha
  rw [LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top] at hr
  rw [e₁.finrank_map_eq, LinearMap.finrank_range_dualMap_eq_finrank_range] at hr
  rw [homStep_range_finrank Q F E (-m) (-n) (2-v) hneg,
    homStep_range_finrank Q E F n m v hm] at hr
  exact hr.symm

lemma homDimension_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v = homDimension Q F E (-n) (2-v) := by
  have he := hom_exact_dimension Q E F n v
  have hf := hom_exact_dimension Q F E (-n) (2-v)
  have hs := homSpace_finrank_dual Q E F n v
  have h₁ := homStep_rank_dual Q E F (n-1) n v (by omega)
  have h₂ := homStep_rank_dual Q E F n (n+1) v rfl
  have hh : -(n-1) = -n+1 := by omega
  rw [hh] at h₁
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomInternalSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
lemma homInternalSupport_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (v : ℤ) :
    v ∈ homInternalSupport Q E F ↔ 2-v ∈ homInternalSupport Q F E := by
  rw [mem_homInternalSupport, mem_homInternalSupport]
  constructor
  · rintro ⟨i,j,r,h⟩
    refine ⟨j,i,r.rev, ?_⟩
    have hr := r.isLt
    simp only [Fin.val_rev]
    omega
  · rintro ⟨j,i,r,h⟩
    refine ⟨i,j,r.rev, ?_⟩
    have hr := r.isLt
    simp only [Fin.val_rev]
    omega

omit [Fintype V] [DecidableEq A] in
lemma homSpace_off_internal_support (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) (hv : v ∉ homInternalSupport Q E F) :
    homSpace Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  by_contra hh
  have ha := homogeneous_nonzero_degree Q (hf.2 i j).2 hh
  rw [mem_homInternalSupport] at hv
  apply hv
  refine ⟨i,j,⟨(v + (E.placement i).internal - (F.placement j).internal).toNat, ?_⟩, ?_⟩
  · omega
  · simp only
    omega

omit [Fintype V] [DecidableEq A] in
lemma homDimension_off_internal_support (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) (hv : v ∉ homInternalSupport Q E F) :
    homDimension Q E F n v = 0 := by
  have hs := homSpace_off_internal_support Q E F n v hv
  have hz : homCycles Q E F n v = ⊥ := by
    change homSpace Q E F n v ⊓ _ = _
    rw [hs, bot_inf_eq]
  unfold homDimension
  have : Subsingleton (homCycles Q E F n v) := by rw [hz]; infer_instance
  have : Subsingleton (homCohomology Q E F n v) := inferInstance
  exact Module.finrank_zero_of_subsingleton

lemma totalHomDimension_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) :
    totalHomDimension Q E F t = totalHomDimension Q F E (2-t) := by
  classical
  unfold totalHomDimension
  refine Finset.sum_bij (fun v _ => 2-v) ?_ ?_ ?_ ?_
  · intro v hv
    exact (homInternalSupport_dual Q E F v).mp hv
  · intro a _ b _ h
    omega
  · intro b hb
    have hh := (homInternalSupport_dual Q F E b).mp hb
    exact ⟨2-b, hh, by omega⟩
  · intro v _
    rw [homDimension_dual Q E F (t-v) v]
    congr 1
    omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientTopDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [DecidableEq A] in
lemma pure_top_socle_homDimension_pos (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) (ht : coefficientTopDual Q E α c ≠ ⊥)
    (hs : coefficientSocle Q F α d ≠ ⊥) :
    0 < homDimension Q E F (d-c) (k-l-(d-c)) := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
  obtain ⟨y,hy,hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  let f : homCycles Q E F (d-c) (k-l-(d-c)) :=
    ⟨topSocleMatrix Q α x y, topSocleMatrix_mem_homCycles Q E F hE hF α c d hx hy⟩
  have hf : f ≠ 0 := fun h => topSocleMatrix_ne_zero Q α hx0 hy0 (congrArg Subtype.val h)
  unfold homDimension
  rw [(pureCoefficientCohomology Q E F hE hF (by omega)).finrank_eq]
  exact Module.finrank_pos_iff.mpr ⟨⟨f,0,hf⟩⟩

omit [Fintype V] [DecidableEq A] in
lemma homDimension_le_totalHomDimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v ≤ totalHomDimension Q E F (n+v) := by
  classical
  by_cases hv : v ∈ homInternalSupport Q E F
  · unfold totalHomDimension
    have h' := Finset.single_le_sum (f := fun w => homDimension Q E F (n+v-w) w)
      (fun _ _ => Nat.zero_le _) hv
    simpa only [add_sub_cancel_right] using h'
  · rw [homDimension_off_internal_support Q E F n v hv]
    exact Nat.zero_le _

omit [DecidableEq A] in
lemma pure_top_socle_totalHomDimension_pos (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) (ht : coefficientTopDual Q E α c ≠ ⊥)
    (hs : coefficientSocle Q F α d ≠ ⊥) :
    0 < totalHomDimension Q E F (k-l) := by
  have h := lt_of_lt_of_le (pure_top_socle_homDimension_pos Q E F hE hF α c d ht hs)
    (homDimension_le_totalHomDimension Q E F (d-c) (k-l-(d-c)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UnfoldedPresentation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma unfoldedArtinAction_generator (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (α : V) :
    unfoldedArtinAction Q (K := K) hn M hM (generator M α) =
      classTwistPerm Q hn α := by
  exact PresentedGroup.toGroup.of _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimension2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma unfoldedArtinAction_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M)
    (x : Artin M) (n v : ℤ) (E F : FiniteHomotopyClass Q (K := K)) :
    classHomDimension Q n v (unfoldedArtinAction Q hn M hM x E)
      (unfoldedArtinAction Q hn M hM x F) = classHomDimension Q n v E F := by
  let H : Subgroup (Artin M) := {
    carrier := {x | ∀ E F : FiniteHomotopyClass Q (K := K),
      classHomDimension Q n v (unfoldedArtinAction Q hn M hM x E)
        (unfoldedArtinAction Q hn M hM x F) = classHomDimension Q n v E F}
    one_mem' := by intro E F; simp only [map_one, Equiv.Perm.one_apply]
    mul_mem' := by
      intro x y hx hy E F
      rw [map_mul]
      change classHomDimension Q n v
        (unfoldedArtinAction Q hn M hM x (unfoldedArtinAction Q hn M hM y E))
        (unfoldedArtinAction Q hn M hM x (unfoldedArtinAction Q hn M hM y F)) = _
      rw [hx, hy]
    inv_mem' := by
      intro x hx E F
      have h := hx (unfoldedArtinAction Q hn M hM x⁻¹ E)
        (unfoldedArtinAction Q hn M hM x⁻¹ F)
      rw [map_inv] at h ⊢
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm }
  have h := PresentedGroup.generated_by (braidRelators M) H (by
    intro α E F
    change classHomDimension Q n v
      (unfoldedArtinAction Q hn M hM (generator M α) E)
      (unfoldedArtinAction Q hn M hM (generator M α) F) = _
    rw [unfoldedArtinAction_generator]
    exact classPositiveTwist_homDimension Q hn α n v E F) x
  exact h E F

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InitialProjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma initial_homSpace_nonzero_cochain (α β : V) (n v : ℤ) (hn : n ≠ 0) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  apply (hf.2 i j).1
  change (0 : ℤ) ≠ 0 + n
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Initial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma unfoldedFrame_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    (α β : V) (n v : ℤ) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x β) =
    homDimension Q (initialProjective Q α : BasedComplex Q (K := K) PUnit.{u+1})
      (initialProjective Q β : BasedComplex Q (K := K) PUnit.{u+1}) n v :=
  unfoldedArtinAction_homDimension Q hn M hM x n v (initialClass Q α) (initialClass Q β)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalModelEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classLayerTopDimension_minimal (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (d : ℤ) (α : V) (c : ℤ) :
    classLayerTopDimension Q d α c (classOfComplex Q E) =
      Module.finrank K (coefficientTopDual Q (E.pureLayer Q hE d) α c) :=
  (((minimalClassModelEquivalence Q E).pureLayer Q
    (minimalClassModel_minimal Q _) hE d).coefficientTopDual Q
    (fun i => i.property) (fun j => j.property) α c).finrank_eq

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientTopDualRestrict
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I]

lemma coefficientTopDual_restrict_layer
    (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) (d:ℤ) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientTopDual Q E α c)
    (hs : ∀ i, (E.placement i).level≠d → x i=0) :
    (fun i : {i // (E.placement i).level=d} => x i.val) ∈
      coefficientTopDual Q (E.pureLayer Q hE d) α c := by
  constructor
  · intro i hi; exact hx.1 i.val hi
  · intro i a
    change (∑ j : {i // (E.placement i).level=d}, (E.differential i.val j.val).arrow a * x j.val)=0
    rw [← hx.2 i.val a]
    apply Fintype.sum_of_injective (Subtype.val : {i // (E.placement i).level=d} → I)
      Subtype.val_injective
    · intro j hj
      rw [hs j (fun h => hj ⟨⟨j,h⟩,rfl⟩),MulZeroClass.mul_zero]
    · intro j; rfl

lemma coefficientTopDual_restrict_layer_ne_zero
    (E : BasedComplex Q (K := K) I) (d:ℤ) {x : I → K}
    (hx : x≠0) (hs : ∀ i, (E.placement i).level≠d → x i=0) :
    (fun i : {i // (E.placement i).level=d} => x i.val) ≠ 0 := by
  intro hz
  apply hx
  funext i
  by_cases hi : (E.placement i).level=d
  · exact congrFun hz ⟨i,hi⟩
  · exact hs i hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalEmbedding
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel

universe u

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

theorem exists_minimal_embedding (E : FiniteModel.{u} Q (K := K)) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q E.complex F.complex) ∧
        ∃ e : F.Index ↪ E.Index, ∀ i, F.complex.placement i = E.complex.placement (e i) := by
  have h : ∀ n (B : FiniteModel.{u} Q (K := K)), Fintype.card B.Index = n →
      ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
        Nonempty (HomotopyEquivalence Q B.complex F.complex) ∧
          ∃ e : F.Index ↪ B.Index,
            ∀ i, F.complex.placement i = B.complex.placement (e i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hn
      by_cases hm : B.complex.IsMinimal Q
      · exact ⟨B, hm, ⟨HomotopyEquivalence.refl Q B.complex⟩,
          Function.Embedding.refl _, fun _ => rfl⟩
      · obtain ⟨p⟩ := scalarPivot_of_not_minimal Q B.complex hm
        let C := ofComplex Q (p.reduced Q)
        have hc : Fintype.card C.Index < n := by
          dsimp only [C, ofComplex]
          rw [← hn]
          exact p.retained_card_lt Q
        obtain ⟨F, hF, ⟨e⟩, j, hj⟩ := ih (Fintype.card C.Index) hc C rfl
        exact ⟨F, hF, ⟨(p.reductionEquivalence Q).trans Q e⟩,
          j.trans ⟨Subtype.val, Subtype.val_injective⟩, hj⟩
  exact h (Fintype.card E.Index) E rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseWordAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma inverse_positiveWord (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q w (positiveWordAction Q w x)=x := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih =>
    change inverseWordAction Q w ((classTwistPerm Q hn α).symm
      ((classTwistPerm Q hn α) (positiveWordAction Q w x)))=x
    rw [Equiv.symm_apply_apply,ih]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DownClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma lowerTruncation_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    (lowerTruncation Q E hE d).IsMinimal Q := fun i j=>hE i j

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CochainSignSubOne
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma cochainSign_sub_one (n : ℤ) : cochainSign (K:=ℝ) (n-1)= -cochainSign n := by
  have h:=cochainSign_add_one (K:=ℝ) (n-1)
  rw [sub_add_cancel] at h
  linarith

lemma cochainSign_sub_two (n : ℤ) : cochainSign (K:=ℝ) (n-2)=cochainSign n := by
  rw [show n-2=(n-1)-1 by omega,cochainSign_sub_one,cochainSign_sub_one,neg_neg]

omit [DecidableEq A] in
lemma signedCorner_sum (α β : V) :
    (∑ p : Zigzag.CornerPath Q α β, cochainSign (K:=ℝ) (Path.length p.val))=
      unfoldedCartan Q α β := by
  have hs := Finset.sum_subtype (p:=fun p : Path V A => Path.source Q p=α ∧ Path.target Q p=β) (F:=inferInstance)
    ((Finset.univ : Finset (Path V A)).filter (fun p => Path.source Q p=α ∧ Path.target Q p=β))
    (by intro p; simp) (fun p => cochainSign (K:=ℝ) (Path.length p))
  rw [← hs,Finset.sum_filter]
  simp only [Fintype.sum_sum_type,Path.source,Path.target,Path.length]
  simp [cochainSign,unfoldedCartan,Nat.card_eq_fintype_card,Fintype.card_subtype,
    ← Finset.sum_boole,eq_comm]
  have hv : (∑ x : V, if α=x ∧ β=x then (1:ℝ) else 0)=if α=β then 1 else 0 := by
    simp [ite_and, eq_comm]
  have ha : (∑ x : A, if α=Q.source x ∧ β=Q.target x then (-1:ℝ) else 0)=
      -(∑ x : A, if α=Q.source x ∧ β=Q.target x then (1:ℝ) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [hv,ha]
  split_ifs <;> ring

omit [DecidableEq A] in
lemma signedGeneratorVector_mulVec {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    (unfoldedCartan Q *ᵥ signedGeneratorVector Q E) α=
      ∑ i, cochainSign (K:=ℝ) (E.placement i).level * unfoldedCartan Q α (E.placement i).color := by
  simp only [Matrix.mulVec,dotProduct,signedGeneratorVector,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [placementSignedWeight,mul_comm]

lemma signedGeneratorVector_test {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α β : V) :
    signedGeneratorVector Q (E.testComplex Q α) β=
      if α=β then (unfoldedCartan Q *ᵥ signedGeneratorVector Q E) α else 0 := by
  by_cases h : α=β
  · subst β
    rw [ite_eq_left rfl,signedGeneratorVector_mulVec]
    change (∑ t : TestIndex Q E.placement α,
      if α=α then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
        ((E.placement t.1).internal+Path.length t.2.val)) else 0)=_
    simp only [ite_true, if_true,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    have hlev (p : Zigzag.CornerPath Q α (E.placement i).color) :
        (E.placement i).cochain+((E.placement i).internal+Path.length p.val)=
          (E.placement i).level+Path.length p.val := by
      simp only [GeneratorPlacement.level] <;> ring
    simp_rw [hlev,cochainSign_add]
    rw [← Finset.mul_sum,signedCorner_sum]

  · simp [signedGeneratorVector,placementSignedWeight,testComplex,testPlacement,h]

omit [Fintype V] in
lemma placementSignedWeight_raise (a : GeneratorPlacement V) (v : V) :
    placementSignedWeight ⟨a.color,a.cochain+1,a.internal⟩ v= -placementSignedWeight a v := by
  have hh : a.cochain+1+a.internal=a.level+1 := by dsimp [GeneratorPlacement.level]; omega
  simp only [placementSignedWeight,GeneratorPlacement.level,hh,cochainSign_add_one]
  split_ifs <;> simp

omit [DecidableEq A] [Fintype V] in
lemma Map.signedGeneratorVector_cocone {I J : Type u} [Fintype I] [Fintype J]
    {E : BasedComplex Q (K:=K) I} {F : BasedComplex Q (K:=K) J} (f : Map Q E F) :
    signedGeneratorVector Q (f.cocone Q)=signedGeneratorVector Q E-signedGeneratorVector Q F := by
  funext v
  simp only [signedGeneratorVector,Map.cocone,Map.coconePlacement,Fintype.sum_sum_type,
    placementSignedWeight_raise,Finset.sum_neg_distrib,Pi.sub_apply]
  ring

lemma signedGeneratorVector_cotest {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    signedGeneratorVector Q (E.cotestComplex Q α)=signedGeneratorVector Q (E.testComplex Q α) := by
  funext β
  apply Finset.sum_congr rfl
  intro t _
  change (if α=β then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
    ((E.placement t.1).internal+Path.length t.2.val-2)) else 0)=
    (if α=β then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
    ((E.placement t.1).internal+Path.length t.2.val)) else 0)
  rw [← add_sub_assoc,cochainSign_sub_two]

theorem signedGeneratorVector_negativeTwist {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    signedGeneratorVector Q (E.negativeTwist Q α)=rowReflect (unfoldedCartan Q) α
      (signedGeneratorVector Q E) := by
  unfold negativeTwist
  rw [Map.signedGeneratorVector_cocone,signedGeneratorVector_cotest]
  funext β
  simp only [Pi.sub_apply,signedGeneratorVector_test,rowReflect,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply]
  by_cases h : α=β
  · subst β; simp
  · simp [h,Ne.symm h]

lemma classSignedVector_negativeTwist (x : FiniteHomotopyClass Q (K:=K)) (α : V) :
    classSignedVector Q (classNegativeTwist Q α x)=
      rowReflect (unfoldedCartan Q) α (classSignedVector Q x) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact signedGeneratorVector_negativeTwist Q E.complex α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TotalVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_upper_partition {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (hE : E.IsMinimal Q)
    (q : ℤ) (hhi : ∀ i,(E.placement i).level≤q) :
    signedGeneratorVector Q E=signedGeneratorVector Q (lowerTruncation Q E hE (q-1))+
      signedGeneratorVector Q (E.pureLayer Q hE q) := by
  funext v
  simp only [signedGeneratorVector, lowerTruncation, lowRestriction, pureLayer, restrict, Pi.add_apply]
  have hlo : (∑ i : ↑(lowerLevelSet Q E (q-1)),placementSignedWeight (E.placement i) v)=
      ∑ i ∈ Finset.univ.filter (fun i : I=>(E.placement i).level≤q-1),
        placementSignedWeight (E.placement i) v := by
    symm
    apply Finset.sum_subtype
    intro i
    simp [lowerLevelSet]
  have hh : (∑ i : ↑{i : I | (E.placement i).level=q},placementSignedWeight (E.placement i) v)=
      ∑ i ∈ Finset.univ.filter (fun i : I=>(E.placement i).level=q),
        placementSignedWeight (E.placement i) v := by
    symm
    apply Finset.sum_subtype
    intro i
    simp
  rw [hlo,hh]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi:=hhi i
  by_cases he:(E.placement i).level≤q-1
  · have hn:(E.placement i).level≠q := by omega
    simp [he,hn]
  · have hn:(E.placement i).level=q := by omega
    simp [hn]

omit [Fintype V] [DecidableEq A] in
lemma classSignedVector_upper_partition (x : FiniteHomotopyClass Q (K:=K)) (q : ℤ)
    (hhi : ClassUpperBound Q q x) :
    classSignedVector Q x=classSignedVector Q (classLowerTruncation Q (q-1) x)+
      classSignedVector Q (classLayer Q q x) := by
  rw [classSignedVector_minimal Q x]
  exact signedGeneratorVector_upper_partition Q _ (minimalClassModel_minimal Q x) q hhi

lemma rowReflect_sub (C : Matrix V V ℝ) (α : V) (x y : V → ℝ) :
    rowReflect C α (x-y)=rowReflect C α x-rowReflect C α y := by
  simp only [rowReflect,Matrix.mulVec_sub,Pi.sub_apply,sub_smul]
  module

lemma rowReflect_smul (C : Matrix V V ℝ) (α : V) (a : ℝ) (x : V → ℝ) :
    rowReflect C α (a • x)=a • rowReflect C α x := by
  simp only [rowReflect,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,smul_sub,smul_smul]

lemma rowReflectWord_sub (C : Matrix V V ℝ) (w : List V) (x y : V → ℝ) :
    rowReflectWord C w (x-y)=rowReflectWord C w x-rowReflectWord C w y := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change rowReflect C α (rowReflectWord C w (x-y))=_
    rw [ih,rowReflect_sub]
    rfl

lemma rowReflectWord_smul (C : Matrix V V ℝ) (w : List V) (a : ℝ) (x : V → ℝ) :
    rowReflectWord C w (a • x)=a • rowReflectWord C w x := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change rowReflect C α (rowReflectWord C w (a • x))=_
    rw [ih,rowReflect_smul]
    rfl

lemma classSignedVector_inverseWord (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    classSignedVector Q (inverseWordAction Q w x)=
      rowReflectWord (unfoldedCartan Q) w.reverse (classSignedVector Q x) := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih =>
    change classSignedVector Q (inverseWordAction Q w (classNegativeTwist Q α x))=_
    rw [ih,classSignedVector_negativeTwist,List.reverse_cons,rowReflectWord_append]
    rfl

theorem canonicalLow_reflected_high_signed (hn : ∀ a,Q.source a≠Q.target a)
    (w : List V) (q : ℤ) (x : FiniteHomotopyClass Q (K:=K))
    (hhi : ClassUpperBound Q q x) :
    classSignedVector Q (classLayer Q q (inverseWordAction Q w x))=
      rowReflectWord (unfoldedCartan Q) w.reverse
        (classSignedVector Q x-classSignedVector Q (canonicalWordLow Q w q x)) := by
  have h:=classSignedVector_upper_partition Q (inverseWordAction Q w x) q
    (inverseWord_upper_bound Q w x hhi)
  have hl : classLowerTruncation Q (q-1) (inverseWordAction Q w x)=
      inverseWordAction Q w (canonicalWordLow Q w q x) :=
    (inverse_positiveWord Q hn w _).symm
  rw [hl,classSignedVector_inverseWord,classSignedVector_inverseWord] at h
  rw [rowReflectWord_sub]
  exact (eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact h.symm))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CanonicalLowReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem canonicalLow_reflected_high (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (hl:ClassLowerBound Q q (canonicalWordLow Q w q x))
    (hh:ClassUpperBound Q q (canonicalWordLow Q w q x)) :
    classTotalVector Q (classLayer Q q (inverseWordAction Q w x))=
      rowReflectWord (unfoldedCartan Q) w.reverse
        (classTotalVector Q x-classTotalVector Q (canonicalWordLow Q w q x)) := by
  have h:=canonicalLow_reflected_high_signed Q hn w q x hhi
  have lower : ClassLowerBound Q q (classLayer Q q (inverseWordAction Q w x)) :=
    classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm)
  have upper : ClassUpperBound Q q (classLayer Q q (inverseWordAction Q w x)) :=
    classUpperBound_of_representative Q _ (fun index => le_of_eq index.property)
  rw [classSignedVector_pure Q _ q lower upper,
    classSignedVector_pure Q x q hlo hhi,classSignedVector_pure Q _ q hl hh,
    ← smul_sub,rowReflectWord_smul] at h
  have h':=congrArg (fun z:V→ℝ=>cochainSign (K:=ℝ) q • z) h
  simpa only [smul_smul,cochainSign_mul_self,one_smul] using h'

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ColorRestrictionTopZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma colorRestriction_top_zero (E:BasedComplex Q (K:=K) I) (q:ℤ) (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U)
    (α:V) (hα:α∈U) (c:ℤ)
    (hz:coefficientTopDual Q (colorRestriction Q E U hp hb) α c=⊥) :
    coefficientTopDual Q E α c=⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x=0
  let y:{i:I // (E.placement i).color∈U}→K:=fun i=>x i
  have hxo (i:I) (hi:(E.placement i).color∉U):x i=0 := by
    apply hx.1 i
    left
    intro h
    exact hi (h ▸ hα)
  have hy:y∈coefficientTopDual Q (colorRestriction Q E U hp hb) α c := by
    constructor
    · intro i hi
      exact hx.1 i hi
    · intro i a
      change (∑ j:{i:I //(E.placement i).color∈U},(E.differential i.val j.val).arrow a*x j.val)=0
      rw [← Finset.sum_subtype (Finset.univ.filter fun j:I=>(E.placement j).color∈U)
        (by simp) (fun j:I=>(E.differential i.val j).arrow a*x j),Finset.sum_filter]
      convert hx.2 i.val a using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj:(E.placement j).color∈U
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj,hxo j hj,MulZeroClass.mul_zero]
  rw [hz] at hy
  have hy0:y=0:=(Submodule.mem_bot K).mp hy
  funext i
  by_cases hi:(E.placement i).color∈U
  · exact congrFun hy0 ⟨i,hi⟩
  · exact hxo i hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HighConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] in
lemma highRestriction_top_eq_layer (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q) :
    classOfComplex Q (upperTruncation Q E hE (q-1))=
      classLayer Q q (classOfComplex Q E) := by
  have he:(upperTruncation Q E hE (q-1)).reindex Q (highPureIndex Q E q hhi)=
      E.pureLayer Q hE q := by
    apply ext_placement_differential Q <;> rfl
  rw [classLayer_minimal]
  exact (classOfComplex_reindex Q _ (highPureIndex Q E q hhi)).trans
    (by rw [he])

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma totalHomDimension_eq_sum_of_subset (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) (D : Finset ℤ)
    (hD : homInternalSupport Q E F ⊆ D) :
    totalHomDimension Q E F t = ∑ v ∈ D, homDimension Q E F (t-v) v := by
  unfold totalHomDimension
  apply Finset.sum_subset hD
  intro v _ hv
  exact homDimension_off_internal_support Q E F (t-v) v hv

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimensionRetract
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J T:Type*} [Fintype I] [Fintype J] [Fintype T]
  [DecidableEq I] [DecidableEq J] [DecidableEq T]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] [DecidableEq T] in
lemma totalHomDimension_le_of_pointwise (M:BasedComplex Q (K:=K) T)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (a b:ℤ)
    (h:∀ v,homDimension Q M E (a-v) v ≤ homDimension Q M F (b-v) v) :
    totalHomDimension Q M E a ≤ totalHomDimension Q M F b := by
  classical
  let D:=homInternalSupport Q M E ∪ homInternalSupport Q M F
  rw [totalHomDimension_eq_sum_of_subset Q M E a D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q M F b D Finset.subset_union_right]
  exact Finset.sum_le_sum (fun v _=>h v)

omit [DecidableEq I] [DecidableEq J] in
lemma cappedSummand_total_bound (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (M:BasedComplex Q (K:=K) T) (U:Set V) (q d:ℤ)
    (hM:∀ i,(M.placement i).level=q) (hU:∀ i,(M.placement i).color∈U)
    (ι:Map Q M (E.pureLayer Q hE q)) (π:Map Q (E.pureLayer Q hE q) M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement)
    (hcap:E.CappedOn Q U q)
    (hzero:∀ n v,n+v=d-q → homDimension Q E F n v=0) :
    totalHomDimension Q M (F.pureLayer Q hF d) (d-q) ≤
      totalHomDimension Q (F.pureLayer Q hF (d-1)) M (q-d+1) := by
  have hb:totalHomDimension Q M (F.pureLayer Q hF d) (d-q) ≤
      totalHomDimension Q M (F.pureLayer Q hF (d-1)) (d-q+1) := by
    apply totalHomDimension_le_of_pointwise Q
    intro v
    have f:=cappedSummandInjection Q E F hE hF M U q d (d-q-v) v hM hU ι π
      hret hcap (hzero _ _ (by omega)) (by omega)
    have h:=LinearMap.finrank_le_finrank_of_injective f.property
    change homDimension Q M (F.pureLayer Q hF d) (d-q-v) v ≤
      homDimension Q M (F.pureLayer Q hF (d-1)) (d-q-v+1) v at h
    simpa only [show d-q-v+1=d-q+1-v by omega] using h
  rw [totalHomDimension_dual Q M (F.pureLayer Q hF (d-1)) (d-q+1)] at hb
  simpa only [show 2-(d-q+1)=q-d+1 by omega] using hb

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InitialHomSpaceNegative
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma initial_homSpace_negative (α β : V) (n v : ℤ) (h : n + v < 0) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = ⊥ := by
  by_cases hn : n = 0
  · apply le_antisymm _ bot_le
    intro f hf
    change f = 0
    apply Matrix.ext
    intro i j
    have hh : Homogeneous Q v (f i j) := by
      simpa only [initialProjective, add_zero, sub_zero] using (hf.2 i j).2
    have hv : v < 0 := by omega
    apply Zigzag.ext
    · exact hh.1 (by omega)
    · exact hh.2.1 (by omega)
    · exact hh.2.2 (by omega)
  · exact initial_homSpace_nonzero_cochain Q α β n v hn

lemma frameModel_negative_pair_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α β : V)
    (n v : ℤ) (h : n + v < 0) :
    homDimension Q (frameModel Q (K := K) hn M hM x α).complex
      (frameModel Q hn M hM x β).complex n v = 0 := by
  rw [frameModel, frameModel, minimalClassModel_homDimension, unfoldedFrame_homDimension]
  exact homDimension_zero_of_homSpace_zero Q _ _ n v (initial_homSpace_negative Q α β n v h)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

omit [Fintype V] [DecidableEq A] in
theorem classLayer_eq_of_cone_gap (f:Map Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    classLayer Q q (classOfComplex Q E)=classLayer Q q (classOfComplex Q F) := by
  rw [classLayer_minimal Q E hE,classLayer_minimal Q F hF]
  exact Quotient.sound ⟨(coneLayerIsomorphism Q f hE hF D e q hD).toHomotopyEquivalence Q⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LayerConeEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

omit [Fintype V] [DecidableEq A] in
theorem classLayer_eq_of_cone_equivalence (f:Map Q E F)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    classLayer Q q (classOfComplex Q E)=classLayer Q q (classOfComplex Q F) := by
  let E₀:=minimalClassModel Q (classOfComplex Q E)
  let F₀:=minimalClassModel Q (classOfComplex Q F)
  let a:HomotopyEquivalence Q E₀.complex E:=minimalClassModelEquivalence Q E
  let b:HomotopyEquivalence Q F F₀.complex:=(minimalClassModelEquivalence Q F).symm Q
  let h:=a.forward.comp Q f
  let g:=h.comp Q b.forward
  let c:HomotopyEquivalence Q (g.cone Q) D:=
    (((b.coneTarget Q h).symm Q).trans Q (a.coneSource Q f)).trans Q e
  have hh:=classLayer_eq_of_cone_gap Q g
    (minimalClassModel_minimal Q (classOfComplex Q E))
    (minimalClassModel_minimal Q (classOfComplex Q F)) D c q hD
  have he:classOfComplex Q E₀.complex=classOfComplex Q E:=minimalClassModel_class Q _
  have hf:classOfComplex Q F₀.complex=classOfComplex Q F:=minimalClassModel_class Q _
  exact (congrArg (classLayer Q q) he).symm.trans
    (hh.trans (congrArg (classLayer Q q) hf))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LayerSocleDimensionSum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classLayerTopDimension_sum (x : I → FiniteHomotopyClass Q (K := K))
    (d : ℤ) (α : V) (c : ℤ) :
    classLayerTopDimension Q d α c (classSum Q x) =
      ∑ i, classLayerTopDimension Q d α c (x i) := by
  classical
  let E (i:I) := (minimalClassModel Q (x i)).complex
  have hE (i:I) : (E i).IsMinimal Q := minimalClassModel_minimal Q (x i)
  have hx : x = fun i => classOfComplex Q (E i) := by
    funext i
    exact (minimalClassModel_class Q (x i)).symm
  conv_lhs => rw [hx,classSum_complex]
  rw [classLayerTopDimension_minimal Q _ (finiteSum_minimal Q E hE)]
  rw [((sumLayerComparison Q E hE d).coefficientTopDual Q
    (fun i => i.property) (fun i => i.2.property) α c).finrank_eq]
  rw [(coefficientTopSumEquiv Q (fun i => (E i).pureLayer Q (hE i) d)
    (fun _ x => x.property) α c).finrank_eq,Module.finrank_pi_fintype]
  rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ClosedNeighborhood
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
universe u
variable {V A : Type u} (Q : ReversibleQuiver V A)

namespace Zigzag.BasedComplex
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {K : Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma ClassCapOn.mono {x : FiniteHomotopyClass Q (K:=K)} {U T : Set V} {q : ℤ}
    (h : ClassCapOn Q x U q) (hT : T⊆U) : ClassCapOn Q x T q := fun i hi=>h i (hT hi)

omit [Fintype V] [DecidableEq A] in
lemma classCapOn_of_upper (x : FiniteHomotopyClass Q (K:=K)) (U : Set V) (q : ℤ)
    (h : ClassUpperBound Q q x) : ClassCapOn Q x U q := fun i _=>h i

lemma reducedNegativeAmplitudeTwist_cap {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (U : Set V) (q : ℤ)
    (hcap : ∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q)
    (α : V) (hα : α∈U) :
    ∀ k,((reducedNegativeAmplitudeTwist Q E α).placement k).color∈Q.closedNeighborhood U →
      ((reducedNegativeAmplitudeTwist Q E α).placement k).level≤q := by
  intro k hk
  rw [reducedNegativeAmplitudeTwist_placement] at hk ⊢
  rcases k with p|i
  · have hi:=hcap p.val.1 (Q.corner_target_mem_neighborhood hα p.val.2)
    have hp:=Path.length_cases p.val.2.val
    have hn:=p.property
    dsimp only [GeneratorPlacement.level] at hi ⊢
    rcases hp with hp|hp|hp <;> omega
  · exact hcap i.val hk

theorem classNegativeTwist_capOn (x : FiniteHomotopyClass Q (K:=K))
    (U : Set V) (q : ℤ) (hcap : ClassCapOn Q x (Q.closedNeighborhood U) q)
    (α : V) (hα : α∈U) :
    ClassCapOn Q (classNegativeTwist Q α x) (Q.closedNeighborhood U) q := by
  let E:=minimalClassModel Q x
  let y:=classNegativeTwist Q α x
  let F:=minimalClassModel Q y
  have he : classOfComplex Q (E.complex.negativeTwist Q α)=classOfComplex Q F.complex := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hx : classOfComplex Q E.complex=x := minimalClassModel_class Q x
    have hy : classOfComplex Q F.complex=y := minimalClassModel_class Q y
    rw [hx,hy]
  obtain ⟨e⟩:=Quotient.exact he
  have reduction : HomotopyEquivalence Q (E.complex.negativeTwist Q α)
      (reducedNegativeAmplitudeTwist Q E.complex α) := by
    convert negativeAmplitudeTwistReduction Q E.complex α using 1
    all_goals try with_reducible_and_instances rfl
  exact minimal_bound_transport Q (reducedNegativeAmplitudeTwist Q E.complex α) F.complex
    (minimalClassModel_minimal Q y)
    ((reduction.symm Q).trans Q e)
    (fun p=>p.color∈Q.closedNeighborhood U → p.level≤q)
    (reducedNegativeAmplitudeTwist_cap Q E.complex U q hcap α hα)

lemma inverseWord_capOn (w : List V) (x : FiniteHomotopyClass Q (K:=K))
    (U : Set V) (q : ℤ) (hcap : ClassCapOn Q x (Q.closedNeighborhood U) q)
    (hw : ∀ α∈w,α∈U) :
    ClassCapOn Q (inverseWordAction Q w x) (Q.closedNeighborhood U) q := by
  induction w generalizing x with
  | nil => exact hcap
  | cons α w ih =>
    exact ih _ (classNegativeTwist_capOn Q x U q hcap α (hw α (by simp)))
      (fun β hβ=>hw β (by simp [hβ]))

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeTwistModern
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] in
lemma classLayer_eq_self_of_pure (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (h:∀ i,(E.placement i).level=q) :
    classLayer Q q (classOfComplex Q E)=classOfComplex Q E := by
  rw [classLayer_minimal Q E hE]
  have he:(E.pureLayer Q hE q).reindex Q (allPureIndex Q E q h)=E := by
    apply ext_placement_differential Q <;> rfl
  exact (classOfComplex_reindex Q _ (allPureIndex Q E q h)).trans (by rw [he])

omit [Fintype V] [DecidableEq A] in
lemma classLayer_idempotent (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    classLayer Q q (classLayer Q q x)=classLayer Q q x := by
  let y:=classLayer Q q x
  let E:=minimalClassModel Q y
  have hp:∀ i,(E.complex.placement i).level=q := fun i=>
    le_antisymm (classLayer_upperBound Q x q i) (classLayer_lowerBound Q x q i)
  have he:classOfComplex Q E.complex=y:=minimalClassModel_class Q y
  simpa only [he] using classLayer_eq_self_of_pure Q E.complex
    (minimalClassModel_minimal Q y) q hp

omit [Fintype V] [DecidableEq A] in
lemma classLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (q:ℤ) :
    classLayer Q q (classOfComplex Q (lowerTruncation Q E hE q))=
      classLayer Q q (classOfComplex Q E) := by
  apply classLayer_eq_of_cone_equivalence Q (lowInclusion Q E _ (levelDownClosed Q E hE q))
    (upperTruncation Q E hE q) (lowConeReduction Q E _ _) q
  intro j
  have hj:=j.property
  change ¬(E.placement j).level≤q at hj
  change (E.placement j).level≠q-1 ∧ (E.placement j).level≠q
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma capped_upperTruncation_far (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (U:Set V) (q:ℤ)
    (hcap:∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q) :
    ∀ i,((upperTruncation Q E hE q).placement i).color∉Q.closedNeighborhood U := by
  intro i hi
  exact i.property (hcap i hi)

lemma negativeLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (U:Set V) (q:ℤ)
    (hcap:∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q)
    (α:V) (hα:α∈U) :
    classLayer Q q (classOfComplex Q ((lowerTruncation Q E hE q).negativeTwist Q α))=
      classLayer Q q (classOfComplex Q (E.negativeTwist Q α)) := by
  let f:=lowInclusion Q E _ (levelDownClosed Q E hE q)
  let R:=upperTruncation Q E hE q
  have coneIso : ChainIsomorphism Q ((f.cone Q).negativeTwist Q α)
      ((f.negativeTwist Q α).cone Q) := by
    convert negativeTwistCone Q f α using 1
    all_goals try with_reducible_and_instances rfl
  let e:HomotopyEquivalence Q ((f.negativeTwist Q α).cone Q) R:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      (((lowConeReduction Q E (lowerLevelSet Q E q) (levelDownClosed Q E hE q)).negativeTwistModern Q α).trans Q
        (negativeTwistFar Q R U (capped_upperTruncation_far Q E hE U q hcap) α hα))
  apply classLayer_eq_of_cone_equivalence Q (f.negativeTwist Q α) R e q
  intro j
  have hj:=j.property
  change ¬(E.placement j).level≤q at hj
  change (E.placement j).level≠q-1 ∧ (E.placement j).level≠q
  omega

lemma negativeLayer_top (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q) (α:V) :
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q E))=
      classLayer Q q (classNegativeTwist Q α (classLayer Q q (classOfComplex Q E))) := by
  let f:=highProjection Q E _ (levelDownClosed Q E hE (q-1))
  let D:=(highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q
  let G:=minimalClassModel Q (classOfComplex Q (D.negativeTwist Q α))
  let e₀:HomotopyEquivalence Q (D.negativeTwist Q α) G.complex:=
    (minimalClassModelEquivalence Q (D.negativeTwist Q α)).symm Q
  have hd:∀ i,(D.placement i).level≤q-2 := by
    intro i
    rw [highConeRetained_level]
    have hi:=i.property
    change (E.placement i).level≤q-1 at hi
    omega
  have hg:∀ i,(G.complex.placement i).level≤q-2 :=
    negativeTwist_upper_bound Q D G.complex hd α (minimalClassModel_minimal Q _) e₀
  have coneIso : ChainIsomorphism Q ((f.cone Q).negativeTwist Q α)
      ((f.negativeTwist Q α).cone Q) := by
    convert negativeTwistCone Q f α using 1
    all_goals try with_reducible_and_instances rfl
  let e:HomotopyEquivalence Q ((f.negativeTwist Q α).cone Q) G.complex:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      ((((highConeReduction Q E (lowerLevelSet Q E (q-1)) (levelDownClosed Q E hE (q-1))).negativeTwistModern Q α)).trans Q e₀)
  have hh:=classLayer_eq_of_cone_equivalence Q (f.negativeTwist Q α) G.complex e q
    (fun i=>by have hi:=hg i; constructor <;> omega)
  change classLayer Q q (classNegativeTwist Q α (classOfComplex Q E))=
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q (upperTruncation Q E hE (q-1)))) at hh
  rwa [highRestriction_top_eq_layer Q E hE q hhi] at hh

lemma classNegativeTwist_capped_layer (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x (Q.closedNeighborhood U) q)
    (α:V) (hα:α∈U) :
    classLayer Q q (classNegativeTwist Q α x)=
      classLayer Q q (classNegativeTwist Q α (classLayer Q q x)) := by
  let E:=minimalClassModel Q x
  have hE:=minimalClassModel_minimal Q x
  let L:=lowerTruncation Q E.complex hE q
  have hx:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  have hl:=negativeLayer_lowerTruncation Q E.complex hE U q hcap α hα
  have ht:=negativeLayer_top Q L (lowerTruncation_minimal Q E.complex hE q) q
    (fun i=>i.property) α
  have he:=classLayer_lowerTruncation Q E.complex hE q
  change classLayer Q q (classNegativeTwist Q α (classOfComplex Q L))=
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q E.complex)) at hl
  rw [hx] at hl he
  exact hl.symm.trans (ht.trans (congrArg (fun y=>classLayer Q q (classNegativeTwist Q α y)) he))

theorem inverseWord_capped_layer (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x (Q.closedNeighborhood U) q)
    (hw:∀ α∈w,α∈U) :
    classLayer Q q (inverseWordAction Q w x)=
      classLayer Q q (inverseWordAction Q w (classLayer Q q x)) := by
  induction w generalizing x with
  | nil=>exact (classLayer_idempotent Q x q).symm
  | cons α w ih=>
    have hα:=hw α (by simp)
    have hw':∀ β∈w,β∈U:=fun β hβ=>hw β (by simp [hβ])
    have hc:=classNegativeTwist_capped_layer Q x U q hcap α hα
    have hy:=classCapOn_of_upper Q (classLayer Q q x) (Q.closedNeighborhood U) q
      (classLayer_upperBound Q x q)
    exact (ih _ (classNegativeTwist_capOn Q x U q hcap α hα) hw').trans
      ((congrArg (fun y=>classLayer Q q (inverseWordAction Q w y)) hc).trans
        (ih _ (classNegativeTwist_capOn Q _ U q hy α hα) hw').symm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PacketPermAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a, Q.source a ≠ Q.target a)
  (M:CoxeterMatrix V) (hM:UnfoldedPresentation Q M)
local notation "Act" => unfoldedArtinAction Q (K:=K) hn M hM

lemma classPacketPerm_in_action {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv := by
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    rw [classPacketPerm_reindex Q hn v hv e]
    exact ih _ _
  · intro v hv
    refine ⟨1,?_⟩
    rw [map_one,classPacketPerm_empty]
    rfl
  · intro J inst ih v hv
    obtain ⟨x,hx⟩:=ih (v ∘ some) (fun a b hab=>hv (fun he=>hab (Option.some.inj he)))
    refine ⟨generator M (v none)*x,?_⟩
    rw [map_mul,unfoldedArtinAction_generator,hx,classPacketPerm_cons]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PacketTwistRaisedGenerator2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J P : Type u} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J] [DecidableEq P]

theorem packetTwist_raised_generator_top_at_local_cap
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l : ℤ} (U:Set V)
    (hE : ∀ i, (E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤l)
    (v:P → V) (hv:∀ a,v a∈U)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q (E.packetTwist Q v) F)
    (j:J) (hj : (F.placement j).level=l+1)
    (hcol:(F.placement j).color∈Q.closedNeighborhood U) :
    ∃ a:P, ∃ x:I → K,
      x ∈ coefficientTopDual Q E (v a) ((F.placement j).cochain+1) ∧ x≠0 ∧
      ∀ i, (E.placement i).level≠l → x i=0 := by
  obtain ⟨x,hx,hxs,hxd⟩ := minimal_generator_dual_cycle Q (E.packetTwist Q v) F hF e j
  have hxold i : x (Sum.inr i)=0 := by
    apply hxs
    intro he
    have hl := congrArg GeneratorPlacement.level he
    change (E.placement i).level = (F.placement j).level at hl
    have hc: (E.placement i).color=(F.placement j).color := congrArg GeneratorPlacement.color he
    have hb := hE i (hc.symm ▸ hcol)
    rw [hj] at hl
    omega
  have hex : ∃ z, x z≠0 := not_forall.mp (fun h => hx (funext h))
  obtain ⟨⟨a,u⟩|i,hz⟩ := hex
  swap
  · exact (hz (hxold i)).elim
  have hp : (E.packetTwist Q v).placement (Sum.inl ⟨a,u⟩)=F.placement j :=
    Classical.not_not.mp (fun h => hz (hxs _ h))
  have hα : (F.placement j).color=v a := (congrArg GeneratorPlacement.color hp).symm
  let y : TestIndex Q E.placement (v a) → K := fun i => x (Sum.inl ⟨a,i⟩)
  have hplace (i : TestIndex Q E.placement (v a))
      (he : (E.packetTwist Q v).placement (Sum.inl ⟨a,i⟩)=F.placement j) :
      (E.placement i.1).cochain=(F.placement j).cochain+1 ∧
        Path.length i.2.val=2 ∧ (E.placement i.1).level=l := by
    have hc := congrArg GeneratorPlacement.cochain he
    have hu := congrArg GeneratorPlacement.internal he
    change (E.placement i.1).cochain-1=(F.placement j).cochain at hc
    change (E.placement i.1).internal+Path.length i.2.val=(F.placement j).internal at hu
    have hl := hE i.1 (Q.corner_target_mem_neighborhood (hv a) i.2)
    have hr : Path.length i.2.val≤2 := by
      rcases Path.length_cases i.2.val with h|h|h <;> omega
    dsimp only [GeneratorPlacement.level] at hl hj ⊢
    exact ⟨by omega,by omega,by omega⟩
  have hys i : ¬ ((E.placement i.1).cochain=(F.placement j).cochain+1 ∧
      Path.length i.2.val=2) → y i=0 := by
    intro hi
    apply hxs
    intro he
    exact hi ⟨(hplace i he).1,(hplace i he).2.1⟩
  have hyd : Matrix.vecMul y
      (testMatrix Q E.placement E.placement (v a) E.differential).transpose=0 := by
    funext i
    have hh := hxd (Sum.inl ⟨a,i⟩)
    rw [hα,Fintype.sum_sum_type,Fintype.sum_sigma] at hh
    have ht k : ((E.packetTwist Q v).differential (Sum.inl ⟨a,i⟩) (Sum.inl ⟨a,k⟩)).vertex (v a) =
        -testMatrix Q E.placement E.placement (v a) E.differential i k := by
      change (-(packetDifferential Q E.placement v E.differential) ⟨a,i⟩ ⟨a,k⟩).vertex (v a) = _
      rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
      change -(testMatrix Q E.placement E.placement (v a) E.differential i k *
        (vertexId Q (K := K) (v a)).vertex (v a)) = _
      simp [vertexId_eval]
    have htne b (hb:b≠a) (k:TestIndex Q E.placement (v b)) :
        ((E.packetTwist Q v).differential (Sum.inl ⟨a,i⟩) (Sum.inl ⟨b,k⟩)).vertex (v a)=0 := by
      change (-(packetDifferential Q E.placement v E.differential) ⟨a,i⟩ ⟨b,k⟩).vertex (v a) = _
      rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb),neg_zero]
      rfl
    rw [Finset.sum_eq_single a] at hh
    · simp only [ht,hxold,MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,
        neg_mul,Finset.sum_neg_distrib,neg_eq_zero] at hh
      simpa only [Matrix.vecMul,Matrix.transpose_apply,dotProduct,mul_comm,Pi.zero_apply] using hh
    · intro b hb hba
      simp only [htne b hba,MulZeroClass.zero_mul,Finset.sum_const_zero]
    · simp
  have hy : y ∈ topTestCycles Q E (v a) ((F.placement j).cochain+1) := ⟨hys,hyd⟩
  refine ⟨a,sumTokenTest Q E.placement (v a) y, sumTokenTest_top Q E (v a) _ hy, ?_, ?_⟩
  · intro hzero
    have hyz : y=0 := by
      rw [← tokenTestVector_sum Q E.placement (v a) _ y hys,hzero,map_zero]
    exact hz (congrFun hyz u)
  · intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    apply hxs
    intro he
    exact hi (hplace ⟨i,z⟩ he).2.2

theorem packetTwist_local_cap_of_top_zero
    (E : BasedComplex Q (K := K) I) (hmin : E.IsMinimal Q) {l : ℤ}
    (U:Set V)
    (hE : ∀ i, (E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤l)
    (v:P → V) (hv:∀ a,v a∈U)
    (htop : ∀ a c, coefficientTopDual Q (E.pureLayer Q hmin l) (v a) c=⊥) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.packetTwist Q v) F.complex) ∧
      ∀ j, (F.complex.placement j).color∈Q.closedNeighborhood U →
        (F.complex.placement j).level≤l := by
  let B := FiniteModel.ofComplex Q (E.packetTwist Q v)
  obtain ⟨F,hF,⟨e⟩,f,hf⟩ := B.exists_minimal_embedding Q
  refine ⟨F,hF,⟨e⟩,?_⟩
  intro j hcol
  by_contra hb
  have hj : (F.complex.placement j).level=l+1 := by
    have hmax : (F.complex.placement j).level≤l+1 := by
      rw [hf j] at hcol ⊢
      change ((E.packetTwist Q v).placement (f j)).color∈Q.closedNeighborhood U at hcol
      change ((E.packetTwist Q v).placement (f j)).level≤l+1
      generalize he:f j=k at hcol ⊢
      rcases k with ⟨a,i,p⟩|i
      · change ((E.placement i).cochain-1)+((E.placement i).internal+Path.length p.val)≤l+1
        have hh := hE i (Q.corner_target_mem_neighborhood (hv a) p)
        have hr : Path.length p.val≤2 := by
          rcases Path.length_cases p.val with h|h|h <;> omega
        dsimp only [GeneratorPlacement.level] at hh
        omega
      · have hh := hE i hcol
        change (E.placement i).level≤l+1
        omega
    omega
  obtain ⟨a,x,hx,hxz,hs⟩ := packetTwist_raised_generator_top_at_local_cap Q E F.complex U hE v hv hF e j hj hcol
  have hm := coefficientTopDual_restrict_layer Q E hmin l (v a) _ hx hs
  have hn := coefficientTopDual_restrict_layer_ne_zero Q E l hxz hs
  rw [htop] at hm
  exact hn ((Submodule.mem_bot K).mp hm)

theorem classPacketPerm_local_cap_of_top_zero
    (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) {l:ℤ}
    (hcap:ClassCapOn Q x (Q.closedNeighborhood U) l) (hU:∀ a,v a∈U)
    (htop:∀ a c,classLayerTopDimension Q l (v a) c x=0) :
    ClassCapOn Q (classPacketPerm Q hn v hv x) (Q.closedNeighborhood U) l := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have ht:∀ a c,coefficientTopDual Q (E.complex.pureLayer Q hE l) (v a) c=⊥ := by
    intro a c
    exact Submodule.finrank_eq_zero.mp (htop a c)
  obtain ⟨F,hF,⟨e⟩,hb⟩:=packetTwist_local_cap_of_top_zero Q E.complex hE U hcap v hU ht
  have hh:ClassCapOn Q (classOfComplex Q F.complex) (Q.closedNeighborhood U) l :=
    minimal_bound_transport Q F.complex _ (minimalClassModel_minimal Q _)
      (minimalClassModelEquivalence Q F.complex).symm (fun p=>p.color∈Q.closedNeighborhood U→p.level≤l) hb
  have hx:classPacketPerm Q hn v hv x=classOfComplex Q F.complex := by
    rw [← minimalClassModel_class Q x,classPacketPerm_apply]
    exact classOfComplex_eq Q e
  rw [hx]
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TotalVectorLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classLayer_eq_self_of_bounds (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q q x) : classLayer Q q x=x := by
  have h:=classLayer_eq_self_of_pure Q (minimalClassModel Q x).complex
    (minimalClassModel_minimal Q x) q (fun i=>le_antisymm (hh i) (hl i))
  have hx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [hx] at h
  exact h

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_pure_apply (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q q x) (α:V) :
    classTotalVector Q x α=(classLevelArray Q x (α,q):ℝ) := by
  exact (congrArg (fun y=>classTotalVector Q y α) (classLayer_eq_self_of_bounds Q x q hl hh)).symm.trans
    (classTotalVector_layer_apply Q x q α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UnfoldedCartanSymm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open scoped _root_.Matrix

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

variable {I : Type*} [Fintype I]

omit [Fintype V] [DecidableEq A] in
lemma generatorVector_eq_zero_off (E : BasedComplex Q (K := K) I) (active : Set V)
    (hs : ∀ i, (E.placement i).color ∈ active) (α : V) (hα : α ∉ active) :
    generatorVector Q E α = 0 := by
  rw [generatorVector_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hne : (E.placement i).color ≠ α := fun h => hα (h ▸ hs i)
  simp only [ite_eq_right hne]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ComplexPureLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
attribute [local instance] Classical.propDecidable
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classMap_topDimension (x:FiniteHomotopyClass Q (K := K)) (d:ℤ) (α:V) (c:ℤ) :
    classLayerTopDimension R d (e.vertex α) c (e.classMap x) =
      classLayerTopDimension Q d α c x := by
  let E := (minimalClassModel Q x).complex
  have hE := minimalClassModel_minimal Q x
  have hx : classOfComplex Q E = x := minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLayerTopDimension_minimal Q E hE,
    classLayerTopDimension_minimal R (e.complex E) (e.complex_minimal hE),← e.complex_pureLayer]
  exact (e.coefficientTopDual (E.pureLayer Q hE d) (fun i => i.property) α c).finrank_eq.symm

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_HomDualSupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma coefficientTop_label_dimension
    (E : Zigzag.BasedComplex U (K := K) T) {l:ℤ}
    (hE : ∀ i, (E.placement i).level=l) (u:V) (c:J) (b:ℤ) :
    Module.finrank K (Zigzag.BasedComplex.coefficientTopDual U (C E) (u,c) b) =
      ∑ a : {a:J // N a c}, Module.finrank K (Zigzag.BasedComplex.coefficientTopDual U E (u,a) b) := by
  rw [(coefficientTopLabelEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE u c b).finrank_eq]
  exact Module.finrank_pi_fintype K

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LayerIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]

lemma classLayerTopDimension_label (d : ℤ) (x : FiniteHomotopyClass U (K := K))
    (v:V) (c:J) (b:ℤ) :
    classLayerTopDimension U d (v,c) b (F x) =
      ∑ a : {a:J // N a c}, classLayerTopDimension U d (v,a) b x := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLayerTopDimension_minimal U (C E)
    (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  rw [((layerComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE d).coefficientTopDual U
    (fun i => i.property) (fun i => i.1.property) (v,c) b).finrank_eq,
    coefficientTop_label_dimension Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      (E.pureLayer U hE d) (fun i => i.property)]
  rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_WordOrbitSocleAdjacency
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (hn : ∀ b, Q.source b ≠ Q.target b)
  (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "O" => (fun (w : List (V × Bool)) (s : V) (a : J) =>
  wordPacketPerm Q step hstep N hN hn w (initialClass U (K := K) (s,a)))

include ho hμ hA hroot hPF

lemma wordOrbit_top_adjacency (w : List (V × Bool)) (s v : V) (d b : ℤ) (i j : J) :
    (∑ a : {a // N a j}, classLayerTopDimension U d (v,a) b (O w s i)) =
      ∑ a : {a // N i a}, classLayerTopDimension U d (v,j) b (O w s a) := by
  rw [← classLayerTopDimension_label Q step hstep N hN orient μ A ho hμ δ hA hroot hPF]
  rw [classLabel_wordOrbit Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF,
    classLayerTopDimension_sum]

variable [Nonempty J]
  (hconn : ∀ a b, Relation.ReflTransGen N a b)
  (ρ : J → ℝ) (hρ : ∀ a, 0 < ρ a) (θ : ℝ)
  (hρPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, ρ b = θ * ρ a)

include hconn hρ hρPF

theorem wordOrbit_top_proportional (w : List (V × Bool)) (s v : V) (d b : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, ρ i * (classLayerTopDimension U d (v,j) b (O w s i) : ℝ)) = r * ρ j := by
  apply GraphConnection.nonnegative_eigenvector_proportional N hconn ρ hρ θ hρPF
  · exact GraphConnection.weighted_intertwiner N hN ρ θ hρPF _
      (wordOrbit_top_adjacency Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF w s v d b)
  · intro j
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hρ i)) (Nat.cast_nonneg _)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_StrictChamber
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

theorem dual_chamber_cover (f:(S → ℝ) →ₗ[ℝ] ℝ) :
    ∃ w:W,∃ a:S → ℝ,(∀ i,0 ≤ a i) ∧
      ∀ v:S → ℝ,f v=∑ i,a i*(representation cs w v) i := by
  obtain ⟨p,hp⟩:=exists_strict_chamber cs
  obtain ⟨w,_,hw⟩:=Finset.exists_max_image (Finset.univ:Finset W)
    (fun w=>f (representation cs w p)) Finset.univ_nonempty
  let a:S → ℝ := fun i=>f (representation cs w (Pi.single i 1))
  have ha : ∀ i,0 ≤ a i := by
    intro i
    have h:=hw (w*cs.simple i) (Finset.mem_univ _)
    simp only [map_mul,LinearEquiv.mul_apply,representation_simple,simpleReflection_apply,
      hp,one_smul,map_sub] at h
    dsimp [a]
    linarith
  refine ⟨w⁻¹,a,ha,?_⟩
  intro v
  have hv : representation cs w (representation cs w⁻¹ v)=v := by
    rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  have hv' : representation cs w⁻¹ v=∑ i,(representation cs w⁻¹ v) i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    f v=f (representation cs w (representation cs w⁻¹ v)) := congrArg f hv.symm
    _ = _ := by
      conv_lhs => rw [hv']
      simp only [map_sum,map_smul,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a]
      rw [mul_comm]

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_ChamberInequalitiesConvexHull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

theorem chamber_inequalities_convexHull (σ:W → S → ℝ) (e:S → ℝ)
    (h : ∀ w i,0 ≤ (representation cs w (e-σ w)) i) :
    e ∈ convexHull ℝ (Set.range σ) := by
  by_contra he
  obtain ⟨f,u,heu,hu⟩:=geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range σ)) ((Set.finite_range σ).isClosed_convexHull ℝ) he
  obtain ⟨w,a,ha,hf⟩:=dual_chamber_cover cs f.toLinearMap
  have hdiff : 0 ≤ f (e-σ w) := by
    rw [show f (e-σ w)=∑ i,a i*(representation cs w (e-σ w)) i from hf _]
    exact Finset.sum_nonneg (fun i _=>mul_nonneg (ha i) (h w i))
  have hs:=hu (σ w) (subset_convexHull ℝ (Set.range σ) (Set.mem_range_self w))
  rw [map_sub] at hdiff
  linarith

theorem chamber_inequalities_interior (σ:W → S → ℝ) (e:S → ℝ)
    (h : ∀ w i,0 < (representation cs w (e-σ w)) i) :
    e ∈ interior (convexHull ℝ (Set.range σ)) := by
  let U : Set (S → ℝ) := {x | ∀ w i,0 < (representation cs w (x-σ w)) i}
  have ho : IsOpen U := by
    have hU : U=(⋂ w:W,⋂ i:S,{x:S → ℝ | 0 < (representation cs w (x-σ w)) i}) := by
      ext x
      simp [U]
    rw [hU]
    apply isOpen_iInter_of_finite
    intro w
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun x:S → ℝ=>representation cs w (x-σ w)) :=
      ((representation cs w).toLinearMap.continuous_of_finiteDimensional).comp
      (continuous_id.sub continuous_const)
    exact isOpen_lt continuous_const ((continuous_apply i).comp hc)
  have hsub : U ⊆ convexHull ℝ (Set.range σ) := by
    intro x hx
    exact chamber_inequalities_convexHull cs σ x (fun w i=>(hx w i).le)
  exact interior_maximal hsub ho h

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E)

omit [Fintype V] [DecidableEq V] in
lemma fusionQuiver_arrow_count (hd : ∀ s t, d s t = d t s)
    (α β : FusionVertex (V := V) m) :
    Nat.card {a : FusionQuiverArrow m d // (fusionQuiver m d hd).source a = α ∧
      (fusionQuiver m d hd).target a = β} = (d α.1 β.1).multiplicity m α.2 β.2 := by
  rw [Nat.card_congr (fusionArrowAtEquiv m d hd α β), Nat.card_fin]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_StringAdjacent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver
variable {V B : Type} (Q : ReversibleQuiver V B)
  [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

namespace StringFunctor
open Zigzag.BasedComplex

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (hn : ∀ b, Q.source b ≠ Q.target b) (m : ℕ) (hm : 2 ≤ m)
local notation "N" => stringAdjacent m
local notation "hN" => stringAdjacent_symm m
local notation "U" => Q.stringQuiver step hstep N hN
local notation "O" => (fun (w : List (V × Bool)) (s : V) (a : StringLabel m) =>
  wordPacketPerm Q step hstep N hN hn w (initialClass U (K := ℂ) (s,a)))

include hm

include hn hm

theorem string_wordOrbit_top_proportional (w : List (V × Bool)) (s v : V) (d b : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, stringWeight m i * (classLayerTopDimension U d (v,j) b (O w s i) : ℝ)) =
        r * stringWeight m j := by
  have : NeZero (m-1) := ⟨by omega⟩
  obtain ⟨A,hA,hr,hμ,hPF⟩ := string_connection_exists m hm
  exact wordOrbit_top_proportional Q step hstep N hN hn Q.fixedOrientation
    (fun a => (stringWeight m a : ℂ)) A (Q.fixedOrientation_reverse hn) hμ
    (2 * Real.cos (Real.pi/m) : ℝ) hA hr hPF (stringAdjacent_connected m)
    (stringWeight m) (stringWeight_pos hm) _ (stringAdjacent_weight m hm) w s v d b

end StringFunctor
end ReversibleQuiver
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd

variable (e:E)
local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "W" => StringFunctor.wordPacketPerm Qr step hstep N hN (K:=ℂ) hnr
local notation "O" => fusionPacketOrbit m d hd hdiag

variable (hm:∀ e,2 ≤ m e)

include hm in
lemma fusionOrbit_top_slice (w:List (V × Bool)) (s v:V) (q b:ℤ)
    (r t:FusionLabel mr) : ∃ c:ℝ, ∀ j,
    (∑ i,stringWeight (m e) i *
      (classLayerTopDimension Q q (v,(labelSplit m e).symm (r,j)) b
        (O w s ((labelSplit m e).symm (t,i))):ℝ)) = c*stringWeight (m e) j := by
  obtain ⟨z,hz⟩ := fusionOrbit_split m d hd hdiag e w
  obtain ⟨c,hc,h⟩ := StringFunctor.string_wordOrbit_top_proportional Qr step hstep hnr (m e) (hm e)
    z (s,t) (v,r) q b
  refine ⟨c,fun j=>?_⟩
  calc
    _ = ∑ i,stringWeight (m e) i * (classLayerTopDimension U q ((v,r),j) b
        (W z (initialClass U ((s,t),i))):ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (fusionQuiverSplit m e d hd).classMap_topDimension,hz]
      simp only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
        labelSplit_symm_at,labelSplit_symm_rest]
    _ = _ := h j

include hm

theorem fusionPacketOrbit_top_proportional (w:List (V × Bool)) (s v:V) (q b:ℤ) :
    ∃ c:ℝ,0 ≤ c ∧ ∀ L,
      (∑ H,fusionWeight m H*(classLayerTopDimension Q q (v,L) b (O w s H):ℝ)) =
        c*fusionWeight m L :=
  fusion_weighted_matrix_proportional m hm _
    (fun e=>fusionOrbit_top_slice m d hd hdiag e hm w s v q b)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "C" => fusionOrdinaryMatrix m d hd
local notation "Act" => fusionOrdinaryAction m d hd (K:=K) hdiag

lemma fusionPacket_in_action (s:V) : ∃ x:Artin C,
    Act x=fusionPacketPerm m d hd hdiag s :=
  classPacketPerm_in_action Q (fusionQuiver_no_loops m d hd hdiag) C
    (fusionOrdinaryPresentation m d hd) (fun L=>(s,L)) (fusionColor_orthogonal m d hd hdiag s)

lemma fusionSignedPacket_in_action (a:V × Bool) : ∃ x:Artin C,
    Act x=fusionSignedPacketPerm m d hd hdiag a := by
  obtain ⟨x,hx⟩ := fusionPacket_in_action m d hd hdiag (K:=K) a.1
  cases h:a.2
  · refine ⟨x⁻¹,?_⟩
    rw [map_inv,hx]
    simp [fusionSignedPacketPerm,h]
  · exact ⟨x,by simpa only [fusionSignedPacketPerm,h,↓reduceIte] using hx⟩

lemma fusionWord_in_action (w:List (V × Bool)) : ∃ x:Artin C,
    Act x=fusionWordPacketPerm m d hd hdiag w := by
  induction w with
  | nil => exact ⟨1,map_one Act⟩
  | cons a w ih =>
    obtain ⟨x,hx⟩ := fusionSignedPacket_in_action m d hd hdiag (K:=K) a
    obtain ⟨y,hy⟩ := ih
    exact ⟨x*y,by rw [map_mul,hx,hy]; rfl⟩

lemma fusionOrbit_in_action (w:List (V × Bool)) : ∃ x:Artin C, ∀ s L,
    fusionPacketOrbit m d hd hdiag w s L = unfoldedFrame Q
      (fusionQuiver_no_loops m d hd hdiag) C (fusionOrdinaryPresentation m d hd) x (s,L) := by
  obtain ⟨x,hx⟩ := fusionWord_in_action m d hd hdiag (K:=ℂ) w
  refine ⟨x,fun s L=>?_⟩
  exact congrArg (fun f=> f (initialClass Q (s,L))) hx.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionOrbitModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "C" => fusionOrdinaryMatrix m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

lemma fusionOrbitModel_negative_homDimension (w:List (V × Bool)) (s t:V)
    (L H:FusionLabel m) (n v:ℤ) (h:n+v<0) :
    homDimension Q (fusionOrbitModel m d hd hdiag w s L).complex
      (fusionOrbitModel m d hd hdiag w t H).complex n v=0 := by
  obtain ⟨x,hx⟩:=fusionOrbit_in_action m d hd hdiag w
  let f (a b:FiniteHomotopyClass Q (K:=ℂ)) :=
    homDimension Q (minimalClassModel Q a).complex (minimalClassModel Q b).complex n v
  change f (O w s L) (O w t H)=0
  rw [hx,hx]
  exact
    frameModel_negative_pair_homDimension Q hn C (fusionOrdinaryPresentation m d hd)
      (K:=ℂ) x (s,L) (t,H) n v h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionQuiverCartan
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E)
omit [Fintype V] in

lemma fusionQuiver_cartan (hd : ∀ s t, d s t = d t s) :
    ReversibleQuiver.Zigzag.BasedComplex.unfoldedCartan (fusionQuiver m d hd) =
      fusionUnfoldedCartan m d := by
  ext α β
  simp only [ReversibleQuiver.Zigzag.BasedComplex.unfoldedCartan,
    fusionQuiver_arrow_count, fusionUnfoldedCartan, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.of_apply]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalFusionMultiplicity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)

lemma canonicalFusionMultiplicity_fold (w:List V) (z:List (V×Bool)) (s:V) (q:ℤ)
    (hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L)))) :
    (∑ L,fusionWeight m L • classTotalVector Q (C w q (classLayer Q q (O z s L))))=
      fusionFold m (canonicalFusionMultiplicity m d hd hdiag hm w z s q) := by
  ext ⟨v,L⟩
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [classTotalVector_pure_apply Q _ q (hp _).1 (hp _).2]
  have hc:=(Classical.choose_spec
    (canonicalFusionLow_count_proportional m d hd hdiag hm w z s v q q)).2 L
  simpa only [fusionFold,canonicalFusionMultiplicity,mul_comm] using hc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ArtinActionWordArtin
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "aw" => sourceArtinAction M (K:=K)

lemma sourceArtinAction_wordArtin (u:List S) :
    aw (wordArtin M u)=((fusionExpandedWord (fusionLabelSize M)
      (u.map (Sum.inl : S→S⊕Unit))).map (classTwistPerm Q (K:=K) hn)).prod := by
  have hh:=fusionExpandedWord_perm (fusionLabelSize M) (coxeterFusionEdge M)
    (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)
    (u.map (Sum.inl : S→S⊕Unit))
  rw [fusionWordPacketPerm_positive] at hh
  have ha: aw (wordArtin M u)=
      ((u.map (Sum.inl : S→S⊕Unit)).map
        (fusionPacketPerm (fusionLabelSize M) (coxeterFusionEdge M)
          (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))).prod := by
    simp only [wordArtin,map_list_prod,List.map_map,sourceArtinAction_generator,Function.comp_def]
  refine ha.trans (hh.symm.trans ?_)
  exact congrArg (fun h : DecidableEq (FusionQuiverArrow (fusionLabelSize M) (coxeterFusionEdge M)) =>
    ((fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))).map
      (@classTwistPerm _ _ K Q _ _ _ _ h hn)).prod) (Subsingleton.elim _ _)

lemma sourceArtinAction_positiveWord (u:List S) (x:FiniteHomotopyClass Q (K:=K)) :
    aw (wordArtin M u) x=positiveWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))) x := by
  rw [sourceArtinAction_wordArtin,positiveWordAction_eq_prod Q hn]

lemma sourceArtinAction_negativeWord (u:List S) (x:FiniteHomotopyClass Q (K:=K)) :
    aw (wordArtin M u)⁻¹ x=inverseWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))) x := by
  apply (aw (wordArtin M u)).injective
  rw [map_inv]
  change (aw (wordArtin M u)) ((aw (wordArtin M u)).symm x)=_
  rw [Equiv.apply_symm_apply,sourceArtinAction_positiveWord,positive_inverseWord Q hn]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalLowSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm

lemma sourceCanonicalMultiplicity_support (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) :
    ∀ v,v∉Sum.inl '' J→σ (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z s q v=0 := by
  let w:=u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)
  have hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L))) := fun L=>
    sourceCanonicalLow_pure M J hJ u hu q _ (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)
  have hv:=canonicalFusionMultiplicity_fold m d hd hdiag hm w z s q hp
  intro v hnot
  let H:FusionLabel m:=fun e=>⟨0,by have h:2 ≤ m e:=le_trans (by norm_num) (fusionLabelSize_ge_four M e);omega⟩
  have hz:∀ L,classTotalVector Q (C w q (classLayer Q q (O z s L))) (v,H)=0 := by
    intro L
    apply generatorVector_eq_zero_off Q _ (Set.range (unfoldedInclusion M J))
      (sourceCanonicalLow_support M J u z s q L)
    rintro ⟨⟨j,H'⟩,hh⟩
    have he:Sum.inl (j:S)=v:=congrArg Prod.fst hh
    exact hnot ⟨j,j.property,he⟩
  have hval:=congrFun hv (v,H)
  simp only [Finset.sum_apply,Pi.smul_apply,hz,smul_zero,Finset.sum_const_zero,fusionFold] at hval
  exact (mul_eq_zero.mp hval.symm).resolve_left (ne_of_gt (fusionWeight_pos m hm H))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RootExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix Geometric CoxeterExchange
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

omit [Fintype V] in
lemma rootExtension_apply (f:I→V) (hf:Function.Injective f) (x:I→ℝ) (i:I) :
    rootExtension f x (f i)=x i := by
  simp only [rootExtension,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  simp_rw [hf.eq_iff]
  simp

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_outside (f:I→V) (x:I→ℝ) (v:V) (hv:v∉Set.range f) :
    rootExtension f x v=0 := by
  simp only [rootExtension,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hi:v≠f i:=fun h=>hv ⟨i,h.symm⟩
  simp only [ite_eq_right hi,mul_zero]

omit [Fintype V] in
lemma rootExtension_restrict (f:I→V) (hf:Function.Injective f) (x:V→ℝ)
    (hx:∀ v,v∉Set.range f→x v=0) : rootExtension f (x∘f)=x := by
  ext v
  by_cases hv:v∈Set.range f
  · obtain ⟨i,rfl⟩:=hv
    exact rootExtension_apply f hf _ i
  · rw [rootExtension_outside f _ v hv,hx v hv]

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_sub (f:I→V) (x y:I→ℝ) :
    rootExtension f (x-y)=rootExtension f x-rootExtension f y := by
  simp only [rootExtension,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_smul (f:I→V) (r:ℝ) (x:I→ℝ) :
    rootExtension f (r • x)=r • rootExtension f x := by
  simp only [rootExtension,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

omit [Fintype V] in
lemma rootExtension_single (f:I→V) (i:I) :
    rootExtension f (Pi.single i 1)=Pi.single (f i) 1 := by
  simp [rootExtension,Pi.single_apply]

omit [DecidableEq I] in
lemma rootExtension_mulVec (C:Matrix V V ℝ) (f:I→V) (x:I→ℝ) (i:I) :
    (C *ᵥ rootExtension f x) (f i)=(C.submatrix f f *ᵥ x) i := by
  unfold rootExtension
  rw [Matrix.mulVec_sum]
  simp only [Finset.sum_apply,Matrix.mulVec_smul,Pi.smul_apply,Matrix.mulVec_single,
    Matrix.col,Matrix.transpose_apply,Matrix.mulVec,dotProduct,
    Matrix.submatrix_apply,smul_eq_mul]
  simp [MulOpposite.op_one,one_smul,mul_comm]

lemma rowReflect_rootExtension (C:Matrix V V ℝ) (f:I→V) (i:I) (x:I→ℝ) :
    rowReflect C (f i) (rootExtension f x)=rootExtension f (rowReflect (C.submatrix f f) i x) := by
  simp only [rowReflect,rootExtension_mulVec,rootExtension_sub,rootExtension_smul,rootExtension_single]

lemma rowReflectWord_rootExtension (C:Matrix V V ℝ) (f:I→V) (w:List I) (x:I→ℝ) :
    rowReflectWord C (w.map f) (rootExtension f x)=
      rootExtension f (rowReflectWord (C.submatrix f f) w x) := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change rowReflect C (f i) (rowReflectWord C (w.map f) (rootExtension f x))=_
    rw [ih,rowReflect_rootExtension]
    rfl

lemma rowReflectWord_harmonic (C:Matrix V V ℝ) (w:List V) (p:V→ℝ)
    (hp:∀ i∈w,(C *ᵥ p) i=0) : rowReflectWord C w p=p := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change rowReflect C i (rowReflectWord C w p)=p
    rw [ih (fun j hj=>hp j (by simp [hj]))]
    simp only [rowReflect,hp i (by simp),zero_smul,sub_zero]

variable {S:Type*} [Fintype S] [LinearOrder S]

omit [Fintype S] [LinearOrder S] in
lemma sourceRootInclusion_injective (J:Set S) : Function.Injective (sourceRootInclusion J) :=
  fun _ _ h=>Subtype.ext (Sum.inl.inj h)

omit [Fintype S] in
lemma source_folded_submatrix (M:CoxeterMatrix S) (J:Set S) :
    (fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M)).submatrix
      (sourceRootInclusion J) (sourceRootInclusion J)=cartan (restrictedMatrix M J) := by
  have hC : fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M)=framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    exact Subsingleton.elim _ _
  rw [hC]
  ext i j
  simp only [Matrix.submatrix_apply,sourceRootInclusion,framedCartan,cartan,restrictedMatrix_apply,
    Subtype.ext_iff]
  congr 1

lemma sourceRoot_word_representation (M:CoxeterMatrix S) (J:Set S) (w:List J) (x:J→ℝ) :
    rowReflectWord (fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M))
      (w.map (sourceRootInclusion J)) (rootExtension (sourceRootInclusion J) x)=
    rootExtension (sourceRootInclusion J)
      (representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd w) x) := by
  rw [rowReflectWord_rootExtension,source_folded_submatrix,
    rowReflectWord_representation (restrictedMatrix M J).toCoxeterSystem]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CappedReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "C" => canonicalFusionLow (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

theorem source_capped_reflected_high (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hcap:ClassCapOn Q x (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    classTotalVector Q (classLayer Q q (inverseWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))) x))=
    rowReflectWord (unfoldedCartan Q)
      (fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))).reverse
      (classTotalVector Q (classLayer Q q x)-classTotalVector Q
        (C (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) q (classLayer Q q x))) := by
  let w:=fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))
  rw [inverseWord_capped_layer Q w x (Set.range (unfoldedInclusion M J)) q hcap
    (unfolded_full_word_mem M J u)]
  have lower : ClassLowerBound Q q (classLayer Q q x) :=
    classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm)
  have upper : ClassUpperBound Q q (classLayer Q q x) :=
    classUpperBound_of_representative Q _ (fun index => le_of_eq index.property)
  have hp:=sourceCanonicalLow_pure M J hJ u hu q (classLayer Q q x)
    lower upper
  rw [sourceCanonicalLow_eq] at hp ⊢
  exact canonicalLow_reflected_high Q hn w q (classLayer Q q x)
    lower upper hp.1 hp.2

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_NegativePrepend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "P" => fusionWordPacketPerm m d hd hdiag (K:=K)

lemma fusionExpandedInverse_action (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q (fusionExpandedWord m w) x=(P (w.map fun s=>(s,true))).symm x := by
  apply (P (w.map fun s=>(s,true))).injective
  rw [Equiv.apply_symm_apply,← fusionExpandedWord_action,positive_inverseWord Q hn]

lemma fusionPacketOrbit_negativePrepend (w:List V) (z:List (V×Bool)) (s:V) (L:FusionLabel m) :
    fusionPacketOrbit m d hd hdiag (negativePrepend w z) s L=
      inverseWordAction Q (fusionExpandedWord m w) (fusionPacketOrbit m d hd hdiag z s L) := by
  simp only [fusionPacketOrbit,negativePrepend,fusionWordPacketPerm_append,fusionWordPacketPerm_inverse]
  rw [fusionExpandedInverse_action]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RowReflectWordReverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

lemma rowReflectWord_reverse_orthogonal (C:Matrix V V ℝ) (l:List V)
    (hn:l.Nodup) (ho:∀ α∈l,∀ β∈l,α≠β→C α β=0) (x:V→ℝ) :
    rowReflectWord C l.reverse x=rowReflectWord C l x := by
  rw [rowReflectWord_orthogonal C l hn ho,
    rowReflectWord_orthogonal C l.reverse (List.nodup_reverse.mpr hn)
      (by simpa only [List.mem_reverse] using ho)]
  simp only [List.toFinset_reverse]

lemma rowReflect_add (C:Matrix V V ℝ) (α:V) (x y:V→ℝ) :
    rowReflect C α (x+y)=rowReflect C α x+rowReflect C α y := by
  simp only [rowReflect,Matrix.mulVec_add,Pi.add_apply,add_smul]
  module

lemma rowReflectWord_add (C:Matrix V V ℝ) (w:List V) (x y:V→ℝ) :
    rowReflectWord C w (x+y)=rowReflectWord C w x+rowReflectWord C w y := by
  induction w with
  | nil=>rfl
  | cons α w ih=>
    change rowReflect C α (rowReflectWord C w (x+y))=_
    rw [ih,rowReflect_add]
    rfl

lemma rowReflectWord_zero (C:Matrix V V ℝ) (w:List V) : rowReflectWord C w 0=0 := by
  have h:=rowReflectWord_smul C w 0 (0:V→ℝ)
  simpa only [zero_smul] using h

lemma rowReflectWord_sum {F:Type*} (C:Matrix V V ℝ) (w:List V) (t:Finset F) (f:F→V→ℝ) :
    rowReflectWord C w (∑ i∈t,f i)=∑ i∈t,rowReflectWord C w (f i) := by
  induction t using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,rowReflectWord_zero]
  | @insert i t hi ih=>rw [Finset.sum_insert hi,Finset.sum_insert hi,rowReflectWord_add,ih]

variable {E:Type*} [Fintype E] [DecidableEq E] (m:E→ℕ)

lemma fusion_reverse_reflection_intertwining (hm:∀ e,2 ≤ m e)
    (d:V→V→FusionEdge E) (hdiag:∀ i,d i i=.units 0) (i:V) (p:V→ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d)
      (((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L))).reverse)
      (fusionFold m p)=fusionFold m (rowReflect (fusionFoldedCartan m d) i p) := by
  let l:=((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))
  have hn:l.Nodup:=List.Nodup.map (fun _ _ h=>Prod.mk.inj h |>.2) (Finset.nodup_toList _)
  have ho:∀ α∈l,∀ β∈l,α≠β→fusionUnfoldedCartan m d α β=0 := by
    rintro α hα β hβ hne
    obtain ⟨L,_,rfl⟩:=List.mem_map.mp hα
    obtain ⟨L',_,rfl⟩:=List.mem_map.mp hβ
    simp [fusionUnfoldedCartan,hne,hdiag,FusionEdge.multiplicity]
  rw [rowReflectWord_reverse_orthogonal _ l hn ho]
  exact fusion_reflection_intertwining m hm d hdiag i p

theorem fusion_reverse_word_intertwining (hm:∀ e,2 ≤ m e)
    (d:V→V→FusionEdge E) (hdiag:∀ i,d i i=.units 0) (w:List V) (p:V→ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d) (fusionExpandedWord m w).reverse (fusionFold m p)=
      fusionFold m (rowReflectWord (fusionFoldedCartan m d) w.reverse p) := by
  induction w generalizing p with
  | nil=>rfl
  | cons i w ih=>
    change rowReflectWord (fusionUnfoldedCartan m d)
      ((((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L))) ++
        fusionExpandedWord m w).reverse) (fusionFold m p)=_
    rw [List.reverse_append,rowReflectWord_append,fusion_reverse_reflection_intertwining m hm d hdiag,ih,
      List.reverse_cons,rowReflectWord_append]
    rfl

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma fusionFold_sub (x y:V→ℝ) : fusionFold m (x-y)=fusionFold m x-fusionFold m y := by
  ext α
  simp only [fusionFold,Pi.sub_apply,mul_sub]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma fusionFold_injective (hm:∀ e,2 ≤ m e) : Function.Injective (fusionFold (V:=V) m) := by
  intro x y h
  let L:FusionLabel m:=fun e=>⟨0,by have := hm e; omega⟩
  funext v
  have hh:=congrFun h (v,L)
  exact mul_left_cancel₀ (ne_of_gt (fusionWeight_pos m hm L)) hh

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightedReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm

theorem source_weighted_reflected_high (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hcap:∀ L,ClassCapOn Q (O z s L)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    μ (negativePrepend (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z) s q=
      rowReflectWord (fusionFoldedCartan m d) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)).reverse
        (μ z s q-σ (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z s q) := by
  let w:=u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)
  let A:=fun L=>classTotalVector Q (classLayer Q q (O z s L))
  let B:=fun L=>classTotalVector Q (C w q (classLayer Q q (O z s L)))
  have hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L))) := by
    intro label
    exact sourceCanonicalLow_pure M J hJ u hu q _
      (classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm))
      (classUpperBound_of_representative Q _ (fun index => le_of_eq index.property))
  have hA:(∑ L,fusionWeight m L • A L)=fusionFold m (μ z s q) := by
    rw [← fusionOrbitWeightedVector_class,fusionOrbitWeightedVector_eq m d hd hdiag hm]
  have hB:(∑ L,fusionWeight m L • B L)=fusionFold m (σ w z s q) :=
    canonicalFusionMultiplicity_fold m d hd hdiag hm w z s q hp
  apply fusionFold_injective m hm
  calc
    fusionFold m (μ (negativePrepend w z) s q)=
        ∑ L,fusionWeight m L • classTotalVector Q
          (classLayer Q q (inverseWordAction Q (fusionExpandedWord m w) (O z s L))) := by
      rw [← fusionOrbitWeightedVector_eq m d hd hdiag hm,fusionOrbitWeightedVector_class]
      simp only [fusionPacketOrbit_negativePrepend]
      congr 3
      funext L
      congr 9
      exact Subsingleton.elim _ _
    _ = ∑ L,fusionWeight m L • rowReflectWord (unfoldedCartan Q)
        (fusionExpandedWord m w).reverse (A L-B L) := by
      apply Finset.sum_congr rfl
      intro L _
      congr 1
      exact source_capped_reflected_high M J hJ u hu q (O z s L) (hcap L)
    _ = rowReflectWord (unfoldedCartan Q) (fusionExpandedWord m w).reverse
        ((∑ L,fusionWeight m L • A L)-(∑ L,fusionWeight m L • B L)) := by
      rw [← Finset.sum_sub_distrib,rowReflectWord_sum]
      apply Finset.sum_congr rfl
      intro L _
      rw [← smul_sub,rowReflectWord_smul]
    _ = fusionFold m (rowReflectWord (fusionFoldedCartan m d) w.reverse (μ z s q-σ w z s q)) := by
      rw [hA,hB,← fusionFold_sub,fusionQuiver_cartan]
      exact fusion_reverse_word_intertwining m hm d hdiag w _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RootInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

omit [Fintype S] [LinearOrder S] in
lemma sourceRootInclusion_range (J:Set S) : Set.range (sourceRootInclusion J)=Sum.inl '' J := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩; exact ⟨j,j.property,rfl⟩
  · rintro ⟨j,hj,rfl⟩; exact ⟨⟨j,hj⟩,rfl⟩

theorem source_chamber_identity (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v) (j:J) :
    μ (negativePrepend (u.map (sourceRootInclusion J)) z) s q (.inl (j:S))-p (.inl (j:S))=
      representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd u.reverse)
        ((μ z s q-p)∘sourceRootInclusion J-
          (σ (u.map (sourceRootInclusion J)) z s q)∘sourceRootInclusion J) j := by
  let f:=sourceRootInclusion J
  let a:=μ z s q
  let b:=σ (u.map f) z s q
  have hs:∀ v,v∉Sum.inl '' J→b v=0:=sourceCanonicalMultiplicity_support M J hJ u hu z s q
  have hv:∀ v,v∉Set.range f→((a-b)-p) v=0 := by
    intro v hv
    have hn:v∉Sum.inl '' J:=by simpa only [f,sourceRootInclusion_range] using hv
    simp only [Pi.sub_apply,a,hext v hn,hs v hn,sub_zero,sub_self]
  have hfix:rowReflectWord C (u.map f).reverse p=p := by
    apply rowReflectWord_harmonic
    intro v hv
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp hv)
    exact hp i
  have href:μ (negativePrepend (u.map f) z) s q=rowReflectWord C (u.map f).reverse (a-b) := by
    convert source_weighted_reflected_high M J hJ u hu z s q hcap using 1 <;>
      congr 9
  have hvec:μ (negativePrepend (u.map f) z) s q-p=
      rootExtension f (representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd u.reverse)
        ((a-p)∘f-b∘f)) := by
    conv_lhs => rw [href,← hfix,← rowReflectWord_sub]
    rw [← rootExtension_restrict f (sourceRootInclusion_injective J) ((a-b)-p) hv]
    have he:(((a-b)-p)∘f)=((a-p)∘f-b∘f) := by ext i; simp only [Function.comp_apply,Pi.sub_apply] <;> ring
    rw [he,← List.map_reverse]
    exact sourceRoot_word_representation M J u.reverse _
  have hval:=congrFun hvec (f j)
  rw [rootExtension_apply f (sourceRootInclusion_injective J)] at hval
  exact hval

lemma source_negative_representative (J:Set S) (u:List J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    ∃ g∈artinParabolic M J,
      (∀ L,O (negativePrepend (u.map (sourceRootInclusion J)) z) s L=
        sourceArtinAction M g (O z s L)) ∧
      (∀ L,ClassCapOn Q (O (negativePrepend (u.map (sourceRootInclusion J)) z) s L)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) := by
  let a:=wordArtin M (u.map Subtype.val)
  have ha:a∈artinParabolic M J:=wordArtin_mem_parabolic M J _
    (by intro i hi;obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi;exact j.property)
  refine ⟨a⁻¹,(artinParabolic M J).inv_mem ha,?_,?_⟩
  · intro L
    rw [fusionPacketOrbit_negativePrepend,sourceArtinAction_negativeWord]
    simp only [List.map_map,Function.comp_def]
    congr 9
    exact Subsingleton.elim _ _
  · intro L
    rw [fusionPacketOrbit_negativePrepend]
    convert inverseWord_capOn Q _ _ _ q (hcap L) (unfolded_full_word_mem M J u) using 1
    all_goals try with_reducible_and_instances rfl
    congr 9
    exact Subsingleton.elim _ _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_ConvexWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

omit [Fintype S] [LinearOrder S] in
lemma sourceConvexWord_reverse (J:Set S) (w:(restrictedMatrix M J).Group) :
    (restrictedMatrix M J).toCoxeterSystem.wordProd (sourceConvexWord M J w).reverse=w := by
  rw [CoxeterSystem.wordProd_reverse]
  have h:(restrictedMatrix M J).toCoxeterSystem.wordProd (sourceConvexWord M J w)=w⁻¹:=
    wordCoxeter_reducedExpression _ _
  rw [h,inv_inv]

lemma sourceConvexModel_counts (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) :
    (∑ L,fusionWeight m L • generatorVector Q (sourceConvexModel M J z s q w L).complex)=
      fusionFold m (sourceConvexVector M J z s q w) := by
  apply canonicalFusionMultiplicity_fold
  intro L
  exact sourceCanonicalLow_pure M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) q _ (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)

lemma sourceConvexVector_support (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) :
    ∀ v,v∉Sum.inl '' J→sourceConvexVector M J z s q w v=0 :=
  sourceCanonicalMultiplicity_support M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) z s q

lemma sourceConvex_representative (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v) (w:(restrictedMatrix M J).Group) :
    ∃ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) ∧
      (∀ j:J,fusionFamilyMultiplicity m d hd hm (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))-
        p (.inl (j:S))=representation (restrictedMatrix M J).toCoxeterSystem w
          ((μ z s q-p)∘sourceRootInclusion J-(sourceConvexVector M J z s q w)∘sourceRootInclusion J) j) := by
  obtain ⟨g,hg,he,hc⟩:=source_negative_representative M J (sourceConvexWord M J w) z s q hcap
  have he':(fun L=>sourceArtinAction M g (O z s L))=
      O (negativePrepend ((sourceConvexWord M J w).map (sourceRootInclusion J)) z) s :=
    funext (fun L=>(he L).symm)
  refine ⟨g,hg,fun L=>he L ▸ hc L,?_⟩
  intro j
  rw [he',fusionFamilyMultiplicity_orbit]
  have h:=source_chamber_identity M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) z s q p hcap hp hext j
  rw [sourceConvexWord_reverse] at h
  exact h

theorem source_convex_subobjects_interior (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,p (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    ((μ z s q-p)∘sourceRootInclusion J)∈interior (convexHull ℝ
      (Set.range fun w=>(sourceConvexVector M J z s q w)∘sourceRootInclusion J)) := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  let := Fintype.ofFinite (restrictedMatrix M J).Group
  apply chamber_inequalities_interior (restrictedMatrix M J).toCoxeterSystem
  intro w j
  obtain ⟨g,hg,hc,he⟩:=sourceConvex_representative M J hJ z s q p hcap hp hext w
  rw [← he j]
  exact sub_pos.mpr (huniv g hg hc j)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_InteriorConvexHullReindex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

lemma interior_convexHull_reindex {I J B:Type*} (e:I≃J) (v:J→ℝ) (f:B→J→ℝ)
    (h:(v∘e)∈interior (convexHull ℝ (Set.range fun b=>(f b)∘e))) :
    v∈interior (convexHull ℝ (Set.range f)) := by
  let E:=ContinuousLinearEquiv.piCongrLeft ℝ (fun _:J=>ℝ) e
  have hmap (g:J→ℝ):E (g∘e)=g := by
    exact E.apply_symm_apply g
  have hr:E '' (Set.range fun b=>(f b)∘e)=Set.range f := by
    ext x
    constructor
    · rintro ⟨_,⟨b,rfl⟩,rfl⟩
      exact ⟨b,(hmap (f b)).symm⟩
    · rintro ⟨b,rfl⟩
      exact ⟨(f b)∘e,⟨b,rfl⟩,hmap (f b)⟩
  have hh:E (v∘e)∈E '' interior (convexHull ℝ (Set.range fun b=>(f b)∘e)) := by
    exact ⟨v∘e,h,rfl⟩
  have hi:=E.toHomeomorph.image_interior (convexHull ℝ (Set.range fun b=>(f b)∘e))
  change E '' interior (convexHull ℝ (Set.range fun b=>(f b)∘e))=
    interior (E '' convexHull ℝ (Set.range fun b=>(f b)∘e)) at hi
  have hc:=E.toLinearMap.image_convexHull (Set.range fun b=>(f b)∘e)
  change E '' convexHull ℝ (Set.range fun b=>(f b)∘e)=
    convexHull ℝ (E '' (Set.range fun b=>(f b)∘e)) at hc
  rw [hi,hc,hr,hmap] at hh
  exact hh

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_FusionWeightedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "O" => fusionOrbitModel m d hd hdiag

theorem fusionOrbit_summand_secondary_bound (w:List (V × Bool)) (s:V)
    (L H:FusionLabel m) {T:Type*} [Fintype T] (M:BasedComplex Q (K:=ℂ) T)
    (U:Set (FusionVertex (V:=V) m)) (q k:ℤ)
    (hM:∀ i,(M.placement i).level=q) (hU:∀ i,(M.placement i).color∈U)
    (ι:Map Q M (Y w s L q)) (π:Map Q (Y w s L q) M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement)
    (hcap:(O w s L).complex.CappedOn Q U q) (hk:k<q) :
    totalHomDimension Q M (Y w s H k) (k-q) ≤
      totalHomDimension Q (Y w s H (k-1)) M (q-k+1) := by
  exact cappedSummand_total_bound Q (O w s L).complex (O w s H).complex
    (fusionOrbitModel_minimal m d hd hdiag w s L)
    (fusionOrbitModel_minimal m d hd hdiag w s H) M U q k hM hU ι π hret hcap
    (fun n v h=>fusionOrbitModel_negative_homDimension m d hd hdiag w s s L H n v (by omega))

lemma fusionWeightedHom_nonneg (hm:∀ e,2 ≤ m e) {T R:FusionLabel m → Type*}
    [∀ L,Fintype (T L)] [∀ H,Fintype (R H)]
    (P:∀ L,BasedComplex Q (K:=ℂ) (T L)) (F:∀ H,BasedComplex Q (K:=ℂ) (R H)) (t:ℤ) :
    0≤fusionWeightedHom m d hd P F t := by
  apply Finset.sum_nonneg
  intro L _
  apply Finset.sum_nonneg
  intro H _
  exact mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le (Nat.cast_nonneg _)

theorem fusionOrbit_weighted_secondary_bound (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) {T:FusionLabel m → Type*} [∀ L,Fintype (T L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (U:Set (FusionVertex (V:=V) m)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q) (hU:∀ L i,((M L).placement i).color∈U)
    (ι:∀ L,Map Q (M L) (Y w s L q)) (π:∀ L,Map Q (Y w s L q) (M L))
    (hret:∀ L,(ι L).matrix*(π L).matrix=projectiveIdentity Q (M L).placement)
    (hcap:∀ L,(O w s L).complex.CappedOn Q U q) (hk:k<q) :
    fusionWeightedHom m d hd M (fun H=>Y w s H k) (k-q) ≤
      fusionWeightedHom m d hd (fun H=>Y w s H (k-1)) M (q-k+1) := by
  unfold fusionWeightedHom
  rw [Finset.sum_comm (f:=fun H L=>fusionWeight m H*fusionWeight m L*
    (totalHomDimension Q (Y w s H (k-1)) (M L) (q-k+1):ℝ))]
  apply Finset.sum_le_sum
  intro L _
  apply Finset.sum_le_sum
  intro H _
  rw [mul_comm (fusionWeight m H) (fusionWeight m L)]
  apply mul_le_mul_of_nonneg_left _ (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le
  exact_mod_cast fusionOrbit_summand_secondary_bound m d hd hdiag w s L H (M L) U q k
    (hM L) (hU L) (ι L) (π L) (hret L) (hcap L) hk

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_DimensionNonneg
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "C" => fusionFoldedCartan m d

include hm in
lemma FusionEdge.dimension_nonneg (b:FusionEdge E) : 0≤b.dimension m := by
  let L:FusionLabel m:=fun e=>⟨0,by have:=hm e; omega⟩
  have hs:0≤∑ H,(b.multiplicity m L H:ℝ)*fusionWeight m H :=
    Finset.sum_nonneg (fun H _=>mul_nonneg (Nat.cast_nonneg _) (fusionWeight_pos m hm H).le)
  rw [FusionEdge.dimension_identity m hm] at hs
  exact nonneg_of_mul_nonneg_left hs (fusionWeight_pos m hm L)

include hm in
omit [Fintype V] in
lemma fusionFoldedCartan_off_nonpos (s t:V) (hst:s≠t) : C s t≤0 := by
  simp only [fusionFoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.of_apply,
    ite_eq_right hst,zero_sub]
  exact neg_nonpos.mpr (FusionEdge.dimension_nonneg m hm (d s t))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionOrbitColorSecondary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
include hm
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "O" => fusionPacketOrbit m d hd hdiag

theorem fusionOrbitColor_secondary_bound (w:List (V×Bool)) (s:V) (q k:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (hcap:∀ L,ClassCapOn Q (O w s L) (fusionColorRegion m U) q) (hk:k<q) :
    fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (fun H=>Y w s H k) (k-q) ≤
    fusionWeightedHom m d hd (fun H=>Y w s H (k-1))
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (q-k+1) := by
  let T:=fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L
  let incl L:=blockInclusionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  let proj L:=blockProjectionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  have hret:∀ L,(incl L).matrix*(proj L).matrix=projectiveIdentity Q (T L).placement := by
    intro L
    convert block_inclusion_projection Q (Y w s L q)
      {i | ((Y w s L q).placement i).color∈fusionColorRegion m U} using 1
    · rfl
    · apply Matrix.ext
      intro i j
      simp only [projectiveIdentity,Matrix.diagonal_apply]
      by_cases h:i=j <;> simp only [h,ite_true, if_true,ite_false, if_false]
      rfl
  exact fusionOrbit_weighted_secondary_bound m d hd hdiag hm w s T (fusionColorRegion m U)
    q k (fun L i=>i.val.property) (fun L i=>i.property) incl proj
    (fun L=>by
      convert hret L using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1)
      exact Subsingleton.elim _ _) hcap hk

lemma fusionOrbitColor_Hom_zero_of_previous (w:List (V×Bool)) (s:V) (q k:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (hcap:∀ L,ClassCapOn Q (O w s L) (fusionColorRegion m U) q) (hk:k<q)
    (hz:fusionWeightedHom m d hd (fun H=>Y w s H (k-1))
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (q-k+1)=0) :
    fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (fun H=>Y w s H k) (k-q)=0 := by
  apply le_antisymm
  · exact (fusionOrbitColor_secondary_bound m d hd hdiag hm w s q k U hb hcap hk).trans_eq hz
  · exact fusionWeightedHom_nonneg m d hd hm _ _ _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionProfilePositiveEvery
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (hm:∀ e,2 ≤ m e)
include hm

lemma fusion_profile_positive_every_label (a:FusionLabel m → FusionLabel m → ℕ)
    (ha:∃ c:ℝ,0 ≤ c ∧ ∀ L,(∑ H,fusionWeight m H*(a H L:ℝ))=c*fusionWeight m L)
    {H₀ L₀:FusionLabel m} (h₀:0<a H₀ L₀) (L:FusionLabel m) : ∃ H,0<a H L := by
  obtain ⟨c,_,h⟩:=ha
  have hsum:0 < ∑ H,fusionWeight m H*(a H L₀:ℝ) := by
    apply lt_of_lt_of_le (mul_pos (fusionWeight_pos m hm H₀) (show (0:ℝ)<(a H₀ L₀:ℝ) by exact_mod_cast h₀))
    exact Finset.single_le_sum (fun H _=>mul_nonneg (fusionWeight_pos m hm H).le (Nat.cast_nonneg (a H L₀)))
      (Finset.mem_univ H₀)
  rw [h] at hsum
  have hcpos:0 < c := (mul_pos_iff_of_pos_right (fusionWeight_pos m hm L₀)).mp hsum
  have htarget:0 < ∑ H,fusionWeight m H*(a H L:ℝ) := by
    rw [h]
    exact mul_pos hcpos (fusionWeight_pos m hm L)
  by_contra hn
  push Not at hn
  have hz:∀ H,a H L=0:=fun H=>Nat.eq_zero_of_le_zero (hn H)
  simp only [hz,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero,lt_self_iff_false] at htarget

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionOrbitColorTop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
include hm
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "O" => fusionPacketOrbit m d hd hdiag

theorem fusionOrbitColor_top_socle_Hom_pos (w:List (V×Bool)) (s v:V) (q k b c:ℤ)
    (U:Set V) (hv:v∈U)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    {L₀ H₀ L₁ H₁:FusionLabel m}
    (ht:0 < classLayerTopDimension Q q (v,L₀) b (O w s H₀))
    (hs:0 < classLayerSocleDimension Q k (v,L₁) c (O w s H₁)) :
    0<fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L)
      (fun H=>Y w s H k) (k-q) := by
  obtain ⟨H,htH⟩:=fusion_profile_positive_every_label m hm
    (fun H L=>classLayerTopDimension Q q (v,L) b (O w s H))
    (fusionPacketOrbit_top_proportional m d hd hdiag hm w s v q b) ht L₁
  have hn {I:Type} [Fintype I] (P:Submodule ℂ (I→ℂ))
      (hp:0<Module.finrank ℂ P):P≠⊥ := by
    intro hz
    rw [hz,finrank_bot] at hp
    exact (lt_irrefl 0 hp)
  have htne:coefficientTopDual Q
      (fusionOrbitColorLayer m d hd hdiag w s q U hb H) (v,L₁) b≠⊥ := by
    intro hz
    have hfull:=colorRestriction_top_zero Q (Y w s H q) q (fusionColorRegion m U)
      (fun i=>i.property) (hb H) (v,L₁) hv b hz
    exact hn _ htH hfull
  have hsne:coefficientSocle Q (Y w s H₁ k) (v,L₁) c≠⊥:=hn _ hs
  have hh:=pure_top_socle_totalHomDimension_pos Q
    (fusionOrbitColorLayer m d hd hdiag w s q U hb H) (Y w s H₁ k)
    (fun i=>i.val.property) (fun i=>i.property) (v,L₁) b c htne hsne
  have hnon (L T:FusionLabel m):0≤fusionWeight m L*fusionWeight m T*
      (totalHomDimension Q (fusionOrbitColorLayer m d hd hdiag w s q U hb L)
        (Y w s T k) (k-q):ℝ):=
    mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm T)).le (Nat.cast_nonneg _)
  apply Finset.sum_pos'
  · intro L _
    exact Finset.sum_nonneg (fun T _=>hnon L T)
  · refine ⟨H,Finset.mem_univ H,Finset.sum_pos' (fun T _=>hnon H T) ?_⟩
    refine ⟨H₁,Finset.mem_univ H₁,?_⟩
    exact mul_pos (mul_pos (fusionWeight_pos m hm H) (fusionWeight_pos m hm H₁)) (by exact_mod_cast hh)

theorem fusionOrbitColor_top_zero_of_Hom_zero (w:List (V×Bool)) (s v:V) (q k c:ℤ)
    (U:Set V) (hv:v∈U)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    {L H:FusionLabel m} (hs:0 < classLayerSocleDimension Q k (v,L) c (O w s H))
    (hh:fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L)
      (fun H=>Y w s H k) (k-q)=0) :
    ∀ L' H' b,classLayerTopDimension Q q (v,L') b (O w s H')=0 := by
  intro L' H' b
  by_contra ht
  have hp:=fusionOrbitColor_top_socle_Hom_pos m d hd hdiag hm w s v q k b c U hv hb
    (Nat.pos_of_ne_zero ht) hs
  rw [hh] at hp
  exact lt_irrefl 0 hp

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_NullPatch
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V:Type*}

lemma null_patch [Fintype V] {C:Matrix V V ℝ} (hsym:∀ i j,C i j=C j i)
    (hoff:∀ i j,i≠j→C i j≤0) (I J:Set V) (hJI:J⊆I) (c μ:V→ℝ)
    (hc:∀ i∈I,(C *ᵥ c) i=0)
    (hext:∀ v,(v∈I ∧ v∉J) ∨ (v∉I ∧ ∃ u∈I,C v u<0)→μ v=c v) :
    ∀ j∈J,(C *ᵥ (fun v=>if v∈J then c v else μ v)) j=0 := by
  intro j hj
  rw [← hc j (hJI hj)]
  apply Finset.sum_congr rfl
  intro v _
  change C j v*(if v∈J then c v else μ v)=C j v*c v
  by_cases hv:v∈J
  · rw [ite_eq_left hv]
  · rw [ite_eq_right hv]
    by_cases hi:v∈I
    · rw [hext v (Or.inl ⟨hi,hv⟩)]
    · by_cases hn:C v j<0
      · rw [hext v (Or.inr ⟨hi,j,hJI hj,hn⟩)]
      · have hn':C v j=0:=le_antisymm (hoff v j (fun he=>hi (he ▸ hJI hj))) (le_of_not_gt hn)
        rw [hsym j v,hn',zero_mul,zero_mul]

lemma color_region_exterior (I J:Set V) (c μ:V→ℝ)
    (hc:∀ v,v∉I→c v=0) (hext:∀ v,v∈I→v∉J→μ v=c v) :
    ∀ v,v∉J→(if v∈I then μ v else 0)=c v := by
  intro v hv
  by_cases hi:v∈I
  · rw [ite_eq_left hi,hext v hi hv]
  · rw [ite_eq_right hi,hc v hi]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_IsolatedBoundaryAbsent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "a" => fusionOrbitColorMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

theorem source_isolated_interior (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (c:S⊕Unit→ℝ)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    (fun j:(Sum.inl '' J:Set (S⊕Unit))=>a z s q (Sum.inl '' I) j-c j)∈
      interior (convexHull ℝ (Set.range fun w:(restrictedMatrix M J).Group=>
        (fun j:(Sum.inl '' J:Set (S⊕Unit))=>sourceConvexVector M J z s q w j))) := by
  let p:S⊕Unit→ℝ:=fun v=>if v∈Sum.inl '' J then c v else μ z s q v
  have hi:(Sum.inl '' J:Set (S⊕Unit))⊆Sum.inl '' I := Set.image_mono hJI
  have hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0 := by
    intro j
    apply null_patch (fusionFoldedCartan_symm m d hd) (fusionFoldedCartan_off_nonpos m d hm)
      (Sum.inl '' I) (Sum.inl '' J) hi c (μ z s q) hcNull hdata
    exact ⟨j,j.property,rfl⟩
  have hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v := by
    intro v hv
    exact (ite_eq_right hv).symm
  have hpj (j:J):p (.inl (j:S))=c (.inl (j:S)):=ite_eq_left ⟨j,j.property,rfl⟩
  have hh:=source_convex_subobjects_interior M J hJ z s q p hcap hp hext
    (fun g hg hgc j=>by rw [hpj]; exact huniv g hg hgc j)
  let e:J≃(Sum.inl '' J:Set (S⊕Unit)):=Equiv.Set.image Sum.inl J Sum.inl_injective
  have hv : (fun j:(Sum.inl '' J:Set (S⊕Unit))=>a z s q (Sum.inl '' I) j-c j)∘e =
      (μ z s q-p)∘sourceRootInclusion J := by
    funext j
    change (if Sum.inl (j:S)∈Sum.inl '' I then μ z s q (.inl (j:S)) else 0)-c (.inl (j:S))=
      μ z s q (.inl (j:S))-p (.inl (j:S))
    rw [ite_eq_left ⟨j,hJI j.property,rfl⟩,hpj]
  apply interior_convexHull_reindex e
  rw [hv]
  exact hh

theorem source_isolated_separation (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q k:ℤ) (c:S⊕Unit→ℝ)
    (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀ v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S)))
    (hsoc:∀ H α,α.1∈Sum.inl '' J→∀ r,coefficientSocle Q (Y z s H k) α r=⊥) :
    let hb:=source_isolated_boundary_absent M I J z s q c hcSupp hdata
    (∀ v∉Sum.inl '' I,(∃ u∈Sum.inl '' I,C v u<0)→μ z s k v=0) ∧
    (∀ j∈Sum.inl '' J,(C *ᵥ μ z s k) j=0) ∧
    fusionWeightedHom m d hd (fun L=>fusionOrbitColorLayer m d hd hdiag z s q (Sum.inl '' I) hb L)
      (fun H=>Y z s H k) (k-q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y z s H k)
      (fun L=>fusionOrbitColorLayer m d hd hdiag z s q (Sum.inl '' I) hb L) (q-k)=0 := by
  dsimp only
  apply fusionOrbitColor_subobject_separation_s236 m d hd hdiag hm z s q k
    (Sum.inl '' I) (Sum.inl '' J) (source_isolated_boundary_absent M I J z s q c hcSupp hdata)
    (fun w L=>(sourceConvexModel M J z s q w L).complex)
    (sourceConvexModel_pure M J hJ z s q)
    (fun w L=>by
      convert sourceConvexRegionInclusion M I J hJI hJ z s q
        (source_isolated_boundary_absent M I J z s q c hcSupp hdata) w L using 1)
    c (sourceConvexVector M J z s q)
    (sourceConvexModel_counts M J hJ z s q)
  · intro w L i
    obtain ⟨v,hv⟩:=sourceConvexModel_support M J z s q w L i
    rw [← hv]
    exact ⟨v.1,v.1.property,rfl⟩
  · exact sourceConvexVector_support M J hJ z s q
  · exact hc
  · exact hcSupp
  · exact hcPos
  · exact hcNull
  · exact color_region_exterior (Sum.inl '' I) (Sum.inl '' J) c (μ z s q)
      hcSupp (fun v hv hj=>hdata v (Or.inl ⟨hv,hj⟩))
  · exact source_isolated_interior M I J hJI hJ z s q c hcNull hdata hcap huniv
  · exact hsoc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma closedNeighborhood_mono {V A:Type} (R:ReversibleQuiver V A)
    {U T:Set V} (h:U⊆T) : R.closedNeighborhood U⊆R.closedNeighborhood T := by
  rintro α (hα|⟨β,hβ,a,hs,ht⟩)
  · exact Or.inl (h hα)
  · exact Or.inr ⟨β,h hβ,a,hs,ht⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_IsolatedIterationData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

lemma capJ (z:List ((S⊕Unit)×Bool)) (hc:D.capped z) :
    ∀ L,ClassCapOn Q (O z D.s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M D.J))) D.q := by
  intro L
  apply (hc L).mono
  apply closedNeighborhood_mono
  rw [unfoldedInclusion_range]
  exact fun α hα=>Set.image_mono D.hJI hα

lemma separation (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hs:D.openSocle z k) :
    (∀ v∉Sum.inl '' D.I,(∃ u∈Sum.inl '' D.I,C v u<0)→μ z D.s k v=0) ∧
    (∀ j∈Sum.inl '' D.J,(C *ᵥ μ z D.s k) j=0) ∧
    fusionWeightedHom m d hd (D.fullRegion z hz) (fun H=>Y z D.s H k) (k-D.q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y z D.s H k) (D.fullRegion z hz) (D.q-k)=0 := by
  apply source_isolated_separation M D.I D.J D.hJI D.hJ z D.s D.q k D.c
    D.hc D.hcSupp D.hcPos D.hcNull (D.data z hz) (D.capJ z hc) (D.strict z hz)
  intro H α hα r
  exact Submodule.finrank_eq_zero.mp (hs H α hα r)

lemma cap_move_s236_oai (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hk:k<D.q) (hp:D.openSocle z (k-1)) (j:D.J)
    (hs:∃ H L c,0 < classLayerSocleDimension Q k (.inl j,L) c (O z D.s H)) :
    D.capped ((.inl j,true)::z) := by
  have hrev: fusionWeightedHom m d hd (fun H=>Y z D.s H (k-1))
      (D.fullRegion z hz) (D.q-k+1)=0 := by
    convert (D.separation z hz hc (k-1) hp).2.2.2 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega
  have hf:=fusionOrbitColor_Hom_zero_of_previous m d hd hdiag hm z D.s D.q k
    (Sum.inl '' D.I) (D.boundary z hz)
    (fun L=>ClassCapOn.mono Q (hc L) (fun α hα=>Or.inl hα)) hk hrev
  obtain ⟨H,L,c,hs⟩:=hs
  have ht:=fusionOrbitColor_top_zero_of_Hom_zero m d hd hdiag hm z D.s (.inl j) D.q k c
    (Sum.inl '' D.I) ⟨j,D.hJI j.property,rfl⟩ (D.boundary z hz) hs hf
  intro Hout
  exact classPacketPerm_local_cap_of_top_zero Q hn (fun L=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) (O z D.s Hout) D.region (hc Hout)
    (fun L=>⟨j,D.hJI j.property,rfl⟩) (fun L c=>ht L Hout c)

end IsolatedIterationData
end HarmonicArtin

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.IsolatedIterationData.cap_move_s236_oai := @OAI.HarmonicArtin.IsolatedIterationData.cap_move_s236_oai
