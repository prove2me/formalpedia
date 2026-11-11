-- Prove2me | solution 1 for OAI.HarmonicArtin.sourceGroup_probe_euler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:51:18.676395+00:00
-- url     : https://prove2.me/submissions/38742c7a-6145-4701-b6f3-587ac8c73b86

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag013

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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

lemma homSpace_pure_total_degree_upper (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k)
    (h : k - l + 2 < n + v) : homSpace Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  by_contra he
  have hc : (F.placement j).cochain = (E.placement i).cochain + n := by
    by_contra hc
    exact he ((hf.2 i j).1 hc)
  have ha := homogeneous_nonzero_degree Q (hf.2 i j).2 he
  have he' := hE i
  have hf' := hF j
  dsimp only [GeneratorPlacement.level] at he' hf'
  omega

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpaceDuality
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_LinearMatrix
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomStep
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomInternalSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_PathZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

variable {I J L : Type*}

lemma matrixOne_eq_self {f : Matrix I J (Q.Zigzag K)} (hf : LinearMatrix Q f) :
    matrixOne Q f = f := by
  apply Matrix.ext
  intro i j
  exact pathOne_eq_self Q (hf i j).1 (hf i j).2

lemma matrixOne_mul [Fintype J] (f : Matrix I J (Q.Zigzag K))
    (g : Matrix J L (Q.Zigzag K)) :
    matrixOne Q (f * g) = matrixZero Q f * matrixOne Q g + matrixOne Q f * matrixZero Q g := by
  apply Matrix.ext
  intro i k
  change pathOne Q (∑ j, f i j * g j k) =
    (∑ j, pathZero Q (f i j) * pathOne Q (g j k)) +
    ∑ j, pathOne Q (f i j) * pathZero Q (g j k)
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => pathOne_mul Q _ _

lemma matrixZero_entries {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f) :
    ProjectiveEntries Q p q (matrixZero Q f) := by
  constructor
  · intro i j
    have h := congrArg (pathZero Q) (hf.1 i j)
    rw [pathZero_mul, pathZero_vertexId] at h
    exact h
  · intro i j
    have h := congrArg (pathZero Q) (hf.2 i j)
    rw [pathZero_mul, pathZero_vertexId] at h
    exact h

lemma matrixZero_degree {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {n v : ℤ} {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q p q n v f) :
    MapDegree Q p q n v (matrixZero Q f) := by
  intro i j
  constructor
  · intro h
    change pathZero Q (f i j) = 0
    rw [(hf i j).1 h, map_zero]
  · exact ⟨(hf i j).2.1, fun _ => rfl, fun _ => rfl⟩

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma matrixOne_homDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (g : Matrix I J (Q.Zigzag K)) :
    matrixOne Q (homDifferential Q E F n g) =
      matrixOne Q E.differential * matrixZero Q g -
        cochainSign (K := K) n • (matrixZero Q g * matrixOne Q F.differential) := by
  change matrixOne Q (E.differential * g - cochainSign (K := K) n • (g * F.differential)) = _
  rw [map_sub, map_smul, matrixOne_mul, matrixOne_mul,
    matrixZero_eq_zero Q hE, matrixZero_eq_zero Q hF, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero]

lemma linear_boundary_primitive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hlin : LinearMatrix Q f)
    (hf : f ∈ homBoundaries Q E F n v) :
    ∃ g ∈ homSpace Q E F (n - 1) v,
      (∀ i j, (g i j).arrow = 0 ∧ (g i j).token = 0) ∧
      matrixOne Q E.differential * g - cochainSign (K := K) (n - 1) •
        (g * matrixOne Q F.differential) = f := by
  obtain ⟨g, hg, rfl⟩ := hf
  refine ⟨matrixZero Q g, ⟨matrixZero_entries Q hg.1, matrixZero_degree Q hg.2⟩,
    fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  rw [← matrixOne_homDifferential Q E F hE hF]
  exact matrixOne_eq_self Q hlin

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientSocle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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

lemma coefficient_cocycle_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) (active : Set V)
    (hE : ∀ i, (E.placement i).color ∈ active)
    (hF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v)
    (hc : CoefficientMatrix Q f) : f = 0 := by
  classical
  by_contra hne
  let support : Finset I := Finset.univ.filter fun i => ∃ j, f i j ≠ 0
  have hs : support.Nonempty := by
    by_contra hh
    apply hne
    apply Matrix.ext
    intro i j
    by_contra hz
    exact hh ⟨i, by simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j,hz⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image support (fun i => (E.placement i).cochain) hs
  have hrow : ∀ j, (E.differential * f) i j = 0 := by
    intro j
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t ∈ support
    · have htdeg := hmax t ht
      have hz := (E.degree i t).1 (by omega)
      rw [hz, MulZeroClass.zero_mul]
    · have hz : f t j = 0 := by
        by_contra hh
        exact ht (by simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j,hh⟩)
      rw [hz, MulZeroClass.mul_zero]
  have hout : ∀ j, (f * F.differential) i j = 0 := by
    intro j
    have hh := congrArg (fun m : Matrix I J (Q.Zigzag K) => m i j) hf.2
    change (E.differential*f) i j - cochainSign (K := K) n • (f*F.differential) i j = 0 at hh
    rw [hrow j, zero_sub, neg_eq_zero] at hh
    exact (smul_eq_zero.mp hh).resolve_left (cochainSign_ne_zero (K := K) n)
  let x : J → K := fun j => (f i j).vertex (E.placement i).color
  have hx : x ∈ coefficientSocle Q F (E.placement i).color ((E.placement i).cochain+n) := by
    constructor
    · intro j hj
      rcases hj with hj | hj
      · exact entry_vertex_right_support Q hf.1.1 i j _ (Ne.symm hj)
      · change (f i j).vertex _ = 0
        rw [(hf.1.2 i j).1 hj]
        rfl
    · intro j a ha
      have hh := congrArg (fun z : Q.Zigzag K => z.arrow a) (hout j)
      rw [Matrix.mul_apply, arrow_sum] at hh
      simp only [Finset.sum_apply, arrow_mul, Pi.add_apply, leftScale, rightScale,
        (hc i _).1, Pi.zero_apply, MulZeroClass.zero_mul, add_zero, ha] at hh
      exact hh
  have hxzero : x = 0 := by
    simpa only [hF _ (hE i) _, Submodule.mem_bot] using hx
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hi).2
  apply hj
  exact coefficient_row_zero Q hf.1.1 hc i (fun j => congrFun hxzero j) j

omit [Fintype V] [DecidableEq A] in
lemma pure_coefficient_homDimension_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l k n v : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k) (h : n+v=k-l)
    (active : Set V) (hsE : ∀ i, (E.placement i).color ∈ active)
    (hsF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥) :
    homDimension Q E F n v = 0 := by
  have hz : homCycles Q E F n v = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    exact coefficient_cocycle_zero_of_socle_zero Q E F n v active hsE hsF hf
      (pure_homSpace_coefficient Q E F hE hF h hf.1)
  unfold homDimension
  have : Subsingleton (homCycles Q E F n v) := by rw [hz]; infer_instance
  have : Subsingleton (homCohomology Q E F n v) := inferInstance
  exact Module.finrank_zero_of_subsingleton

omit [Fintype V] [DecidableEq A] in
lemma pure_total_coefficient_homDimension_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l k : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k)
    (active : Set V) (hsE : ∀ i, (E.placement i).color ∈ active)
    (hsF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥) :
    totalHomDimension Q E F (k-l) = 0 := by
  unfold totalHomDimension
  apply Finset.sum_eq_zero
  intro v _
  exact pure_coefficient_homDimension_zero_of_socle_zero Q E F hE hF (by omega)
    active hsE hsF

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_RestrictLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

lemma restrictLayer_matrixOne_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (l k : ℤ)
    (g : Matrix I J (Q.Zigzag K)) :
    restrictLayer Q E F l k (matrixOne Q E.differential * g) =
      (show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * restrictLayer Q E F l k g := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, pathOne Q (E.differential i.val t) * g t j.val) =
    ∑ t : {i // (E.placement i).level = l}, E.differential i.val t.val * g t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (E.placement t).level ≠ (E.placement i.val).level := by
      intro he
      exact ht ⟨⟨t, he.trans i.property⟩, rfl⟩
    rw [pathOne_eq_zero Q (E.differential_arrow_level Q hh), MulZeroClass.zero_mul]
  · intro t
    exact congrArg (fun z : Q.Zigzag K => z * g t.val j.val)
      (pathOne_eq_self Q (E.pureLayer_linear Q hE l i t).1
        (E.pureLayer_linear Q hE l i t).2).symm

lemma restrictLayer_mul_matrixOne (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hF : F.IsMinimal Q) (l k : ℤ)
    (g : Matrix I J (Q.Zigzag K)) :
    restrictLayer Q E F l k (g * matrixOne Q F.differential) =
      restrictLayer Q E F l k g * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential) := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, g i.val t * pathOne Q (F.differential t j.val)) =
    ∑ t : {j // (F.placement j).level = k}, g i.val t.val * F.differential t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (F.placement j.val).level ≠ (F.placement t).level := by
      intro he
      exact ht ⟨⟨t, he.symm.trans j.property⟩, rfl⟩
    rw [pathOne_eq_zero Q (F.differential_arrow_level Q hh), MulZeroClass.mul_zero]
  · intro t
    exact congrArg (fun z : Q.Zigzag K => g i.val t.val * z)
      (pathOne_eq_self Q (F.pureLayer_linear Q hF k t j).1
        (F.pureLayer_linear Q hF k t j).2).symm

lemma layer_boundary_of_extended_boundary (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hlin : LinearMatrix Q f)
    (hf : extendLayer Q E F l k f ∈ homBoundaries Q E F n v) :
    f ∈ homBoundaries Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v := by
  obtain ⟨g, hg, _, he⟩ := linear_boundary_primitive Q E F hE hF n v
    (extendLayer_linear Q E F l k hlin) hf
  refine ⟨restrictLayer Q E F l k g, restrictLayer_homSpace Q E F hE hF l k (n-1) v hg, ?_⟩
  have h := congrArg (restrictLayer Q E F l k) he
  rw [map_sub, map_smul, restrictLayer_matrixOne_mul Q E F hE,
    restrictLayer_mul_matrixOne Q E F hF, restrictLayer_extend] at h
  exact h

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DifferentialMulExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma extendLayer_cycle (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v)
    (hlin : LinearMatrix Q f) :
    extendLayer Q E F l k f ∈ homCycles Q E F n v := by
  refine ⟨extendLayer_homSpace Q E F hE hF l k n v hf.1, ?_⟩
  change homDifferential Q E F n (extendLayer Q E F l k f) = 0
  rw [homDifferential_extendLayer Q E F hE hF l k n hlin, hf.2, map_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma homSpace_finrank (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    Module.finrank K (homSpace Q E F n v) = Nat.card (HomPath Q E F n v) := by
  classical
  rw [(homCoordinatesEquiv Q E F n v).finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CornerPath
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

lemma totalChainDimension_eq_card (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    totalChainDimension Q E F (k-l+r) = Nat.card (CornerPath Q E F r) := by
  classical
  unfold totalChainDimension
  simp_rw [homSpace_finrank, Nat.card_eq_fintype_card]
  rw [← Finset.sum_coe_sort, ← Fintype.card_sigma]
  exact Fintype.card_congr (purePathEquiv Q E F hE hF r)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseWordAction
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureUpperBoundariesZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
lemma pure_upper_boundaries_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : k-l+2 < n+v) : homBoundaries Q E F n v = ⊥ := by
  have hb : homBoundaries Q E F n v ≤ homSpace Q E F n v :=
    (homBoundaries_le_homCycles Q E F n v).trans inf_le_left
  rw [homSpace_pure_total_degree_upper Q E F hE hF h] at hb
  exact le_antisymm hb bot_le

lemma pure_hom_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n+v=k-l) :
    Module.finrank K (homSpace Q E F n v) + Module.finrank K (homSpace Q E F (n+2) v) +
      homDimension Q E F (n+1) v =
    Module.finrank K (homSpace Q E F (n+1) v) + homDimension Q E F n v +
      homDimension Q F E (-(n+2)) (2-v) := by
  have h₀ := hom_exact_dimension Q E F n v
  have h₁ := hom_exact_dimension Q E F (n+1) v
  have h₂ := hom_exact_dimension Q E F (n+2) v
  rw [pure_coefficient_boundaries_zero Q E F hE hF h, finrank_bot] at h₀
  rw [pure_upper_boundaries_zero Q E F hE hF (n := n+2+1) (v := v) (by omega),
    finrank_bot] at h₂
  rw [homDimension_dual Q E F (n+2) v] at h₂
  have hn : n+1+1=n+2 := by omega
  rw [hn] at h₁
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureTotalHomEuler
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

lemma pure_total_hom_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    totalChainDimension Q E F (k-l) + totalChainDimension Q E F (k-l+2) +
      totalHomDimension Q E F (k-l+1) =
    totalChainDimension Q E F (k-l+1) + totalHomDimension Q E F (k-l) +
      totalHomDimension Q F E (l-k) := by
  have hp (v : ℤ) := pure_hom_euler Q E F hE hF (n := k-l-v) (v := v) (by omega)
  have he (v : ℤ) :
      Module.finrank K (homSpace Q E F (k-l-v) v) +
        Module.finrank K (homSpace Q E F (k-l+2-v) v) + homDimension Q E F (k-l+1-v) v =
      Module.finrank K (homSpace Q E F (k-l+1-v) v) +
        homDimension Q E F (k-l-v) v + homDimension Q E F (k-l+2-v) v := by
    have hh := hp v
    rw [← homDimension_dual Q E F (k-l-v+2) v] at hh
    have h₁ : k-l-v+1=k-l+1-v := by omega
    have h₂ : k-l-v+2=k-l+2-v := by omega
    rw [h₁,h₂] at hh
    exact hh
  have hs := Finset.sum_congr (s₁ := homInternalSupport Q E F) (s₂ := homInternalSupport Q E F)
    rfl (fun v _ => he v)
  simp only [Finset.sum_add_distrib] at hs
  change totalChainDimension Q E F (k-l) + totalChainDimension Q E F (k-l+2) +
    totalHomDimension Q E F (k-l+1) = totalChainDimension Q E F (k-l+1) +
    totalHomDimension Q E F (k-l) + totalHomDimension Q E F (k-l+2) at hs
  rw [totalHomDimension_dual Q E F (k-l+2)] at hs
  have h : 2-(k-l+2)=l-k := by omega
  rw [h] at hs
  exact hs

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_EqualColorPair
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

lemma pure_generator_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    2 * Nat.card (EqualColorPair Q E F) + totalHomDimension Q E F (k-l+1) =
      Nat.card (ArrowPair Q E F) + totalHomDimension Q E F (k-l) +
        totalHomDimension Q F E (l-k) := by
  have hh := pure_total_hom_euler Q E F hE hF
  have h₀ := totalChainDimension_eq_card Q E F hE hF 0
  have h₁ := totalChainDimension_eq_card Q E F hE hF 1
  have h₂ := totalChainDimension_eq_card Q E F hE hF 2
  rw [Nat.card_congr (zeroCornerEquiv Q E F)] at h₀
  rw [Nat.card_congr (arrowCornerEquiv Q E F)] at h₁
  rw [Nat.card_congr (tokenCornerEquiv Q E F)] at h₂
  simp only [add_zero] at h₀
  rw [h₀,h₁,h₂] at hh
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
lemma sum_generatorVector (E : BasedComplex Q (K := K) I) (f : V → ℝ) :
    ∑ α, generatorVector Q E α * f α = ∑ i, f (E.placement i).color := by
  classical
  simp only [generatorVector_sum, Finset.sum_mul, ite_mul, _root_.one_mul, MulZeroClass.zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

omit [Fintype V] [DecidableEq A] in
lemma equalColorPair_card (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :
    (Nat.card (EqualColorPair Q E F) : ℝ) =
      ∑ i, ∑ j, if (E.placement i).color = (F.placement j).color then (1 : ℝ) else 0 := by
  classical
  simp only [EqualColorPair, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole,
    Fintype.sum_prod_type]

omit [Fintype V] [DecidableEq A] in
lemma arrowPair_card (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :
    (Nat.card (ArrowPair Q E F) : ℝ) =
      ∑ i, ∑ j, (Nat.card {a : A // Q.source a = (E.placement i).color ∧
        Q.target a = (F.placement j).color} : ℝ) := by
  classical
  simp only [ArrowPair, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole,
    Fintype.sum_prod_type]

omit [DecidableEq A] in
lemma generator_cartan_pairing (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) :
    (generatorVector Q E) ⬝ᵥ ((unfoldedCartan Q).mulVec (generatorVector Q F)) =
      2 * (Nat.card (EqualColorPair Q E F) : ℝ) - Nat.card (ArrowPair Q E F) := by
  classical
  rw [dotProduct, sum_generatorVector]
  simp only [Matrix.mulVec, dotProduct]
  have hs (i : I) :
      ∑ α, unfoldedCartan Q (E.placement i).color α * generatorVector Q F α =
        ∑ j, unfoldedCartan Q (E.placement i).color (F.placement j).color := by
    simpa only [_root_.mul_comm] using
      sum_generatorVector Q F (fun α => unfoldedCartan Q (E.placement i).color α)
  simp_rw [hs, unfoldedCartan]
  rw [equalColorPair_card, arrowPair_card]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> norm_num

lemma pure_cartan_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    (generatorVector Q E) ⬝ᵥ ((unfoldedCartan Q).mulVec (generatorVector Q F)) =
      (totalHomDimension Q E F (k-l) : ℝ) - totalHomDimension Q E F (k-l+1) +
        totalHomDimension Q F E (l-k) := by
  rw [generator_cartan_pairing]
  have hh := pure_generator_euler Q E F hE hF
  have hh' : (2 : ℝ) * Nat.card (EqualColorPair Q E F) + totalHomDimension Q E F (k-l+1) =
      Nat.card (ArrowPair Q E F) + totalHomDimension Q E F (k-l) +
        totalHomDimension Q F E (l-k) := by exact_mod_cast hh
  linarith

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DownClosed
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CochainSignSubOne
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TotalVector
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CanonicalLowReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T] [DecidableEq I]

omit [Fintype V] [DecidableEq A] in
lemma postcomposeOnCycles_injective (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    (ι : TermwiseSplitInjection Q F G) (n v : ℤ) :
    Function.Injective (postcomposeOnCycles Q E F G ι.inclusion n v) := by
  intro f g h
  apply Subtype.ext
  have hh := congrArg (fun f : homCycles Q E G n v => f.val * ι.retraction) h
  change (f.val * ι.inclusion.matrix) * ι.retraction =
    (g.val * ι.inclusion.matrix) * ι.retraction at hh
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ι.split] at hh
  apply Matrix.ext
  intro i j
  have hij := congrArg (fun m : Matrix T I (Q.Zigzag K) => m i j) hh
  simpa only [projectiveIdentity, Matrix.mul_diagonal,
    f.property.1.1.2, g.property.1.1.2] using hij

omit [DecidableEq A] in
lemma pure_coefficient_homDimension_mono (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    {l k n v : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ i, (F.placement i).level = k) (hG : ∀ i, (G.placement i).level = k)
    (h : n+v=k-l) (ι : TermwiseSplitInjection Q F G) :
    homDimension Q E F n v ≤ homDimension Q E G n v := by
  unfold homDimension
  rw [(pureCoefficientCohomology Q E F hE hF h).finrank_eq,
    (pureCoefficientCohomology Q E G hE hG h).finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective
    (postcomposeOnCycles_injective Q E F G ι n v)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma totalHomDimension_eq_sum_of_subset (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) (D : Finset ℤ)
    (hD : homInternalSupport Q E F ⊆ D) :
    totalHomDimension Q E F t = ∑ v ∈ D, homDimension Q E F (t-v) v := by
  unfold totalHomDimension
  apply Finset.sum_subset hD
  intro v _ hv
  exact homDimension_off_internal_support Q E F (t-v) v hv

omit [DecidableEq A] in
lemma pure_total_coefficient_homDimension_mono (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    {l k : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ i, (F.placement i).level = k) (hG : ∀ i, (G.placement i).level = k)
    (ι : TermwiseSplitInjection Q F G) :
    totalHomDimension Q E F (k-l) ≤ totalHomDimension Q E G (k-l) := by
  classical
  let D := homInternalSupport Q E F ∪ homInternalSupport Q E G
  rw [totalHomDimension_eq_sum_of_subset Q E F (k-l) D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E G (k-l) D Finset.subset_union_right]
  apply Finset.sum_le_sum
  intro v _
  exact pure_coefficient_homDimension_mono Q E F G hE hF hG (by omega) ι

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SubobjectMiddleLowerBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix

variable {V A I J T K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [Fintype T] [DecidableEq I] [DecidableEq J] [DecidableEq T]

omit [DecidableEq J] [DecidableEq T] in
lemma subobject_middle_lower_bound (M:BasedComplex Q (K:=K) J)
    (S:BasedComplex Q (K:=K) I) (Y:BasedComplex Q (K:=K) T)
    {q d:ℤ} (hM:∀i,(M.placement i).level=q)
    (hS:∀i,(S.placement i).level=q) (hY:∀i,(Y.placement i).level=d)
    (ι:TermwiseSplitInjection Q S M) (active:Set V)
    (hsS:∀i,(S.placement i).color∈active)
    (hsY:∀α∈active,∀c,coefficientSocle Q Y α c=⊥) :
    generatorVector Q Y ⬝ᵥ ((unfoldedCartan Q).mulVec
      (generatorVector Q S-generatorVector Q M)) ≤
        (totalHomDimension Q Y M (q-d+1):ℝ) := by
  rw [mulVec_sub,dotProduct_sub,pure_cartan_euler Q Y S hY hS,
    pure_cartan_euler Q Y M hY hM]
  have hz:=pure_total_coefficient_homDimension_zero_of_socle_zero Q S Y hS hY active hsS hsY
  have hm:=pure_total_coefficient_homDimension_mono Q Y S M hY hS hM ι
  have hm':(totalHomDimension Q Y S (q-d):ℝ)≤totalHomDimension Q Y M (q-d):=by
    exact_mod_cast hm
  have hn:(0:ℝ)≤totalHomDimension Q Y S (q-d+1):=Nat.cast_nonneg _
  have hp:(0:ℝ)≤totalHomDimension Q M Y (d-q):=Nat.cast_nonneg _
  rw [hz,Nat.cast_zero]
  linarith

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_FamilySubobjectMiddleLower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix

variable {V A T K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype T]
attribute [local instance] Classical.decEq Classical.propDecidable

lemma family_subobject_middle_lower_bound {B H:Type*} [Fintype H]
    (M:H→FiniteModel Q (K:=K)) (Y:BasedComplex Q (K:=K) T)
    {q d:ℤ} (hM:∀h i,((M h).complex.placement i).level=q)
    (hY:∀i,(Y.placement i).level=d)
    (F:B→H→FiniteModel Q (K:=K)) (hF:∀b h i,((F b h).complex.placement i).level=q)
    (ι:∀b h,TermwiseSplitInjection Q (F b h).complex (M h).complex)
    (active:Set V) (hsF:∀b h i,((F b h).complex.placement i).color∈active)
    (hsY:∀α∈active,∀c,coefficientSocle Q Y α c=⊥)
    (ω:H→ℝ) (hω:∀h,0≤ω h) (e:V→ℝ)
    (he:e∈convexHull ℝ (Set.range fun b=>∑h,ω h • generatorVector Q (F b h).complex)) :
    generatorVector Q Y ⬝ᵥ ((unfoldedCartan Q).mulVec
      (e-∑h,ω h • generatorVector Q (M h).complex))≤
      ∑h,ω h*(totalHomDimension Q Y (M h).complex (q-d+1):ℝ) := by
  let L:(V→ℝ)→ₗ[ℝ]ℝ:=
    { toFun:=fun x=>generatorVector Q Y ⬝ᵥ ((unfoldedCartan Q).mulVec x)
      map_add':=fun x y=>by simp only [mulVec_add,dotProduct_add]
      map_smul':=fun r x=>by simp only [mulVec_smul,dotProduct_smul,smul_eq_mul,RingHom.id_apply] }
  let m:V→ℝ:=∑h,ω h • generatorVector Q (M h).complex
  let D:ℝ:=∑h,ω h*(totalHomDimension Q Y (M h).complex (q-d+1):ℝ)
  have hbound (b:B):L (∑h,ω h • generatorVector Q (F b h).complex)-L m≤D := by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun h _=>mul_le_mul_of_nonneg_left
      (subobject_middle_lower_bound Q (M h).complex (F b h).complex Y
        (hM h) (hF b h) hY (ι b h) active (hsF b h) hsY) (hω h))
    change (∑h,ω h*L (generatorVector Q (F b h).complex-generatorVector Q (M h).complex))≤D at hh
    simp only [map_sub,mul_sub,Finset.sum_sub_distrib] at hh
    simpa only [m,map_sum,map_smul,smul_eq_mul,RingHom.id_apply] using hh
  have hinc:Set.range (fun b=>∑h,ω h • generatorVector Q (F b h).complex)⊆L ⁻¹' Set.Iic (D+L m) := by
    rintro x ⟨b,rfl⟩
    exact sub_le_iff_le_add.mp (hbound b)
  have hh:=convexHull_min hinc ((convex_Iic (D+L m)).linear_preimage L) he
  change L (e-m)≤D
  rw [map_sub]
  exact sub_le_iff_le_add.mpr hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HighConeIndex
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_OffDiagonalVertexZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma offDiagonal_vertex_zero {s t:V} {x:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t) : x.vertex=0 := by
  funext v
  by_contra hv
  have h:=coordinates_corner Q hl hr (p:=.inl v) hv
  exact hst (h.1.symm.trans h.2)

lemma offDiagonal_token_zero {s t:V} {x:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t) : x.token=0 := by
  funext v
  by_contra hv
  have h:=coordinates_corner Q hl hr (p:=.inr (.inr v)) hv
  exact hst (h.1.symm.trans h.2)

lemma offDiagonal_radical_mul_zero {s t u:V} {x y:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t)
    (hy:y.vertex=0) (hyr:y*vertexId Q u=y) (hsu:s≠u) : x*y=0 := by
  have hv:=offDiagonal_vertex_zero Q hl hr hst
  have ht: (x*y).token=0 := offDiagonal_token_zero Q
    (by rw [← mul_assoc,hl]) (by rw [mul_assoc,hyr]) hsu
  apply Zigzag.ext
  · simp only [vertex_mul,hv,MulZeroClass.zero_mul,vertex_zero]
  · ext a
    simp only [arrow_mul,hv,hy,leftScale,rightScale,Pi.add_apply,Pi.zero_apply,
      MulZeroClass.zero_mul,MulZeroClass.mul_zero,add_zero,arrow_zero]
  · exact ht

namespace BasedComplex
variable {I:Type*} [Fintype I]

lemma absentProjective_homDifferential_zero (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α)
    (n v:ℤ) {f:Matrix PUnit.{1} I (Q.Zigzag K)}
    (hf:f∈homSpace Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v) :
    homDifferential Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n f=0 := by
  have hm:f*E.differential=0 := by
    apply Matrix.ext
    intro i k
    change (∑j,f i j*E.differential j k)=0
    apply Finset.sum_eq_zero
    intro j _
    exact offDiagonal_radical_mul_zero Q (hf.1.1 i j) (hf.1.2 i j)
      (Ne.symm (ha j)) (hE j k) (E.entries.2 j k) (Ne.symm (ha k))
  change (0:Matrix PUnit.{1} PUnit.{1} (Q.Zigzag K))*f-cochainSign (K:=K) n • (f*E.differential)=0
  rw [hm,Matrix.zero_mul,smul_zero,sub_zero]

lemma absentProjective_homBoundaries_bot (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α) (n v:ℤ) :
    homBoundaries Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨f,hf,rfl⟩
  exact absentProjective_homDifferential_zero Q E hE α ha (n-1) v hf

variable [Fintype V] [DecidableEq A]

lemma absentProjective_homDimension (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α) (n v:ℤ) :
    homDimension Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v=
      Nat.card (HomPath Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v) := by
  have h:=hom_exact_dimension Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v
  rw [absentProjective_homBoundaries_bot Q E hE α ha,
    absentProjective_homBoundaries_bot Q E hE α ha,finrank_bot,
    add_zero,add_zero,homSpace_finrank] at h
  exact h

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ProbeVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type*} (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

namespace Zigzag.BasedComplex
variable {K I:Type*} [Field K] [Fintype V] [Fintype A] [Fintype I]
local notation "R" => probeQuiver Q

lemma probeHomDimension (E:BasedComplex R (K:=K) I) (hE:E.IsMinimal R)
    (α:V) (b:Bool) (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ) :
    homDimension R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v=
      Nat.card (probeCoefficient Q E α n v) := by
  rw [absentProjective_homDimension R E hE _ ha]
  exact Nat.card_congr (probeHomPathEquiv Q E α b ha n v)

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimensionDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

local notation "R" => probeQuiver Q

lemma probeHomDimension_generatorArray {I:Type} [Fintype I]
    (E:BasedComplex R (K:=K) I) (hE:E.IsMinimal R)
    (α:V) (b:Bool) (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ) :
    homDimension R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v=
      E.generatorArray R ⟨.inl α,n,v-1⟩ := by
  rw [probeHomDimension Q E hE α b ha,generatorArray_apply]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => by
    cases E.placement i
    simp only [GeneratorPlacement.mk.injEq]

lemma probeClassHomDimension_generatorArray (x:FiniteHomotopyClass R (K:=K))
    (α:V) (b:Bool)
    (ha:∀i,((minimalClassModel R x).complex.placement i).color≠.inr (α,b)) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) x=
      classGeneratorArray R x ⟨.inl α,n,v-1⟩ := by
  rw [← minimalClassModel_class R x, classGeneratorArray_of_minimal R _
    (minimalClassModel_minimal R x)]
  exact probeHomDimension_generatorArray Q _ (minimalClassModel_minimal R x) α b ha n v

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseMatrix
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LayerConeEquivalence
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ClosedNeighborhood
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeTwistModern
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PlacementLevelFiberSum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable

lemma placementLevel_fiber_sum {V:Type*} (f:GeneratorPlacement V→₀ℕ) (α:V) (d:ℤ) :
    f.mapDomain (fun p=>(p.color,p.level)) (α,d)=
      ∑ p ∈ f.support.filter (fun p=>p.color=α ∧ p.level=d), f p := by
  have h:=Finsupp.mapDomain_apply_eq_sum (fun p:GeneratorPlacement V=>(p.color,p.level)) f
    (a:=⟨α,d,0⟩)
  simp only [GeneratorPlacement.level,add_zero] at h
  apply h.trans
  apply Finset.sum_congr
  · ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hs,he⟩
      exact Finset.mem_filter.mpr ⟨hs,congrArg Prod.fst he,congrArg Prod.snd he⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
      exact Finset.mem_filter.mpr ⟨hs,Prod.ext hc hd⟩
  · intro p hp
    rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TotalHomDimensionReading
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A W I J K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [Fintype J]
attribute [local instance] Classical.decEq Classical.propDecidable

omit [Fintype V] [DecidableEq A] in
lemma totalHomDimension_of_reading (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (f:GeneratorPlacement W→₀ℕ) (α:W)
    (he:∀n v,homDimension Q E F n v=f ⟨α,n,v-1⟩) (t:ℤ) :
    totalHomDimension Q E F t=f.mapDomain (fun p=>(p.color,p.level)) (α,t-1) := by
  rw [totalHomDimension,placementLevel_fiber_sum]
  rw [← Finset.sum_filter_ne_zero (homInternalSupport Q E F)]
  refine Finset.sum_bij (fun v _=>⟨α,t-v,v-1⟩) ?_ ?_ ?_ ?_
  · intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hs,hv⟩
    refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_,rfl,?_⟩
    · rwa [← he]
    · change t-v+(v-1)=t-1
      omega
  · intro a ha b hb hh
    have h:=congrArg GeneratorPlacement.internal hh
    dsimp only at h
    omega
  · rintro ⟨β,n,u⟩ hp
    rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
    dsimp only at hc
    subst β
    change n+u=t-1 at hd
    have hnv:t-(u+1)=n:=by omega
    have huv:u+1-1=u:=by omega
    have hnz:homDimension Q E F (t-(u+1)) (u+1)≠0:=by
      rw [hnv,he,huv]
      exact Finsupp.mem_support_iff.mp hs
    refine ⟨u+1,Finset.mem_filter.mpr ⟨?_,hnz⟩,?_⟩
    · by_contra hv
      exact hnz (homDimension_off_internal_support Q E F _ _ hv)
    · simp only [hnv,huv]
  · intro v hv
    exact he _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TotalVectorLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UnfoldedCartanSymm
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_GeneratorVectorComplex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I:Type u} [Fintype I]
local notation "R" => probeQuiver Q

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma generatorVector_complex (E:BasedComplex Q (K:=K) I) :
    generatorVector R (complex Q E)=Sum.elim (generatorVector Q E) (fun _=>0) := by
  classical
  funext v
  cases v with
  | inl v=>simp only [generatorVector_sum,complex,Function.comp_apply,placement,Sum.inl.injEq,Sum.elim_inl]
  | inr v=>simp only [generatorVector_sum,complex,Function.comp_apply,placement,Sum.inl_ne_inr,
      ite_false, if_false,Finset.sum_const_zero,Sum.elim_inr]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_Path2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
local notation "R" => probeQuiver Q

variable [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma path_coordinates (x:Q.Zigzag K) (p:Path V A) :
    pathCoordinates R (zigzagLinear Q x) (path p)=pathCoordinates Q x p := by
  rcases p with v|a|v <;> rfl

lemma path_basis (p:Path V A) : zigzagLinear Q (pathBasis Q (K:=K) p)=pathBasis R (path p) := by
  apply (pathCoordinates R).injective
  funext q
  rcases q with (v|v)|(a|a)|(v|v)
  · change pathCoordinates Q (pathBasis Q p) (.inl v)=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_vertex,zigzag_vertex_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]
  · change pathCoordinates Q (pathBasis Q p) (.inr (.inl a))=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_arrow,zigzag_arrow_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]
  · change pathCoordinates Q (pathBasis Q p) (.inr (.inr v))=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_token,zigzag_token_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_TestIndex2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type*}
local notation "R" => probeQuiver Q

lemma test_matrix (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testMatrix R (placement ∘ p) (placement ∘ q) (Sum.inl α) (matrix Q M)
      (testIndex Q p α i) (testIndex Q q α j) = testMatrix Q p q α M i j := by
  change pathCoordinates R (pathBasis R (path i.2.val) * zigzagLinear Q (M i.1 j.1))
    (path j.2.val) = _
  rw [← path_basis Q,← zigzagLinear_mul Q,path_coordinates Q]
  rfl

lemma test_transform (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testTransform R (placement ∘ p) (placement ∘ q) (Sum.inl α) (matrix Q M)
      (testIndex Q p α i) (testIndex Q q α j) =
      zigzagLinear Q (testTransform Q p q α M i j) := by
  unfold testTransform scalarCornerMatrix
  rw [test_matrix Q,← zigzag_vertexId Q,map_smul]

lemma evaluation_matrix (p:I → GeneratorPlacement V) (α:V)
    (i:TestIndex Q p α) (j:I) :
    evaluationMatrix R (placement ∘ p) (Sum.inl α) (K := K) (testIndex Q p α i) j =
      zigzagLinear Q (evaluationMatrix Q p α i j) := by
  classical
  change (if i.1=j then pathBasis R (path i.2.val) else 0) = _
  unfold evaluationMatrix
  split_ifs
  · exact (path_basis Q i.2.val).symm
  · exact (map_zero (zigzagLinear Q)).symm

variable [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma positiveTwist_transport (E:BasedComplex Q (K := K) I) (α:V) :
    ((complex Q E).positiveTwist R (Sum.inl α)).reindex R
      ((testIndex Q E.placement α).sumCongr (Equiv.refl I)) =
      complex Q (E.positiveTwist Q α) := by
  apply ext_placement_differential R
  · funext i
    rcases i with i|i
    · change GeneratorPlacement.mk _ _ (_ + Path.length (path i.2.val)) = _
      rw [path_length]
      rfl
    · rfl
  · apply Matrix.ext
    intro i j
    rcases i with i|i <;> rcases j with j|j
    · change -(testTransform R (placement ∘ E.placement) (placement ∘ E.placement)
          (Sum.inl α) (matrix Q E.differential) (testIndex Q E.placement α i)
          (testIndex Q E.placement α j)) = zigzagLinear Q (-testTransform Q _ _ _ _ i j)
      rw [test_transform Q,map_neg]
    · exact evaluation_matrix Q E.placement α i j
    · exact (map_zero (zigzagLinear Q)).symm
    · rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ProbeEmbeddingMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q

lemma classMap_positiveTwist (α:V) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (classPositiveTwist Q α x)=classPositiveTwist R (.inl α) (classMap Q x) := by
  induction x using Quotient.inductionOn with | _ E =>
    change classOfComplex R (complex Q (E.complex.positiveTwist Q α))=
      classOfComplex R ((complex Q E.complex).positiveTwist R (.inl α))
    rw [← positiveTwist_transport]
    exact (classOfComplex_reindex R _ _).symm

omit [Fintype V] [DecidableEq V] [DecidableEq (ProbeVertex V)] in
lemma placement_injective : Function.Injective (placement (V:=V)) := by
  intro p q h
  cases p with | mk v n t => cases q with | mk w m u =>
    simpa only [placement,GeneratorPlacement.mk.injEq,Sum.inl.injEq] using h

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma generatorArray_core {I:Type u} [Fintype I] (E:BasedComplex Q (K:=K) I)
    (p:GeneratorPlacement V) :
    (complex Q E).generatorArray R (placement p)=E.generatorArray Q p := by
  classical
  simp only [generatorArray,Finsupp.finsetSum_apply,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (if placement (E.placement i)=placement p then 1 else 0)=_
  simp only [placement_injective.eq_iff]

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma levelArray_leaf {I:Type u} [Fintype I] (E:BasedComplex Q (K:=K) I) (v:V) (b:Bool) (d:ℤ) :
    (complex Q E).levelArray R (.inr (v,b),d)=0 := by
  classical
  simp only [levelArray_eq_sum,Finsupp.finsetSum_apply,Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i _
  change (if ((.inl (E.placement i).color:ProbeVertex V),(E.placement i).level)=(.inr (v,b),d) then 1 else 0)=0
  simp

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma classGeneratorArray_core (x:FiniteHomotopyClass Q (K:=K)) (p:GeneratorPlacement V) :
    classGeneratorArray R (classMap Q x) (placement p)=classGeneratorArray Q x p := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classGeneratorArray R (classOfComplex R (complex Q E.complex)) _=_
  erw [classGeneratorArray_of_minimal R (FiniteModel.ofComplex R _) (complex_minimal Q hE),
    classGeneratorArray_of_minimal Q E hE]
  exact generatorArray_core Q E.complex p

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma classLevelArray_leaf (x:FiniteHomotopyClass Q (K:=K)) (v:V) (b:Bool) (d:ℤ) :
    classLevelArray R (classMap Q x) (.inr (v,b),d)=0 := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classLevelArray R (classOfComplex R (complex Q E.complex)) _=0
  erw [classLevelArray_of_minimal R (FiniteModel.ofComplex R _) (complex_minimal Q hE)]
  exact levelArray_leaf Q E.complex v b d

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_SignedPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

lemma classMap_absent (x:FiniteHomotopyClass Q (K:=K)) (α:V) (b:Bool) :
    ∀i,((minimalClassModel R (classMap Q x)).complex.placement i).color≠.inr (α,b) := by
  intro i hi
  let E:=minimalClassModel R (classMap Q x)
  let d:ℤ:=(E.complex.placement i).level
  have hz:=classLevelArray_leaf Q x α b d
  rw [← minimalClassModel_class R (classMap Q x),
    classLevelArray_of_minimal R _ (minimalClassModel_minimal R _),levelArray_apply] at hz
  have hh:Nonempty {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}:=⟨⟨i,hi,rfl⟩⟩
  have hp:0<Nat.card {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}:=Nat.card_pos
  change Nat.card {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}=0 at hz
  omega

lemma classHom_dimension (x:FiniteHomotopyClass Q (K:=K)) (α:V) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) (classMap Q x)=
      classGeneratorArray Q x ⟨α,n,v-1⟩ := by
  rw [probeClassHomDimension_generatorArray Q _ α b (classMap_absent Q x α b)]
  exact classGeneratorArray_core Q x ⟨α,n,v-1⟩

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_HomDimensionFlexible
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A] [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q
variable (hn:∀a,Q.source a≠Q.target a)

lemma classHom_dimension_flexible (x:FiniteHomotopyClass Q (K:=K))
    (α:V) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) (classMap Q x)=
      classGeneratorArray Q x ⟨α,n,v-1⟩ := by
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  cases Subsingleton.elim (inferInstance : DecidableEq A) (Classical.decEq A)
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeVertex V))
    (@instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance))
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeArrow V A))
    (@instDecidableEqSum A (V×Bool×Bool) (Classical.decEq A)
      (@instDecidableEqProd V (Bool×Bool) (Classical.decEq V) inferInstance))
  exact classHom_dimension Q x α b n v

lemma classMap_twistProd (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (((w.map (classTwistPerm Q hn)).prod) x)=
      ((w.map (fun v=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl v))).prod)
        (classMap Q x) := by
  induction w generalizing x with
  | nil=>rfl
  | cons a w ih=>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    change classMap Q (classPositiveTwist Q a _) = _
    rw [classMap_positiveTwist,ih]
    rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
local notation "R" => probeQuiver Q

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] [DecidableEq I] in
lemma pureLayer_complex (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (q:ℤ) :
    (complex Q E).pureLayer R (complex_minimal Q hE) q=complex Q (E.pureLayer Q hE q) := by
  apply ext_placement_differential R <;> rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_StrictChamber
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ChamberInequalitiesConvexHull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionVertex
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionQuiverCartan
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalFusionMultiplicity
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ArtinActionWordArtin
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalLowSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RootExtension
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CappedReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_NegativePrepend
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RowReflectWordReverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightedReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RootInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ConvexWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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

theorem source_convex_subobjects (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,p (.inl (j:S))≤fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    ((μ z s q-p)∘sourceRootInclusion J)∈convexHull ℝ
      (Set.range fun w=>(sourceConvexVector M J z s q w)∘sourceRootInclusion J) := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  let := Fintype.ofFinite (restrictedMatrix M J).Group
  apply chamber_inequalities_convexHull (restrictedMatrix M J).toCoxeterSystem
  intro w j
  obtain ⟨g,hg,hc,he⟩:=sourceConvex_representative M J hJ z s q p hcap hp hext w
  rw [← he j]
  exact sub_nonneg.mpr (huniv g hg hc j)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ConvexHullSupportedComp
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

lemma convexHull_of_supported_comp {I V B:Type*} (f:I→V)
    (u:V→ℝ) (s:B→V→ℝ)
    (hu:∀v,v∉Set.range f→u v=0)
    (hs:∀b v,v∉Set.range f→s b v=0)
    (h:(u∘f)∈convexHull ℝ (Set.range fun b=>s b∘f)) :
    u∈convexHull ℝ (Set.range s) := by
  classical
  let E:(I→ℝ)→ₗ[ℝ](V→ℝ):=
    { toFun:=fun x v=>if hv:∃i,f i=v then x (Classical.choose hv) else 0
      map_add':=by intros; funext v; dsimp; split <;> simp
      map_smul':=by intros; funext v; dsimp; split <;> simp }
  have he (x:V→ℝ) (hx:∀v,v∉Set.range f→x v=0):E (x∘f)=x := by
    funext v
    dsimp [E]
    split
    · rename_i hv
      rw [Classical.choose_spec hv]
    · rename_i hv
      exact (hx v hv).symm
  have hh:E (u∘f)∈E '' convexHull ℝ (Set.range fun b=>s b∘f):=⟨_,h,rfl⟩
  rw [E.image_convexHull,← Set.range_comp] at hh
  have hr : (fun b=>E (s b∘f))=s := funext (fun b=>he (s b) (hs b))
  change E (u∘f)∈convexHull ℝ (Set.range (fun b=>E (s b∘f))) at hh
  rwa [he u hu,hr] at hh

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

lemma source_convex_subobjects_full (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,p (.inl (j:S))≤fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    (μ z s q-p)∈convexHull ℝ (Set.range (sourceConvexVector M J z s q)) := by
  have hr:Set.range (sourceRootInclusion J)=Sum.inl '' J := by
    ext v
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.property,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
  apply convexHull_of_supported_comp (sourceRootInclusion J) _ _
  · intro v hv
    rw [hr] at hv
    exact sub_eq_zero.mpr (hext v hv)
  · intro w v hv
    rw [hr] at hv
    exact sourceConvexVector_support M J hJ z s q w v hv
  · exact source_convex_subobjects M J hJ z s q p hcap hp hext huniv

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_MapPacket
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=K)
local notation "bw" => sourceProbeAction M (K:=K)

lemma classMap_sourcePacket (s:S) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (aw (generator M s) x)=sourceProbePacket M s (classMap Q x) := by
  have h:=classMap_twistProd Q hn (K:=K) (fusionExpandedWord m [Sum.inl s]) x
  erw [fusionExpandedWord_perm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)] at h
  simpa only [sourceArtinAction_generator,List.map_cons,List.map_nil,
    fusionWordPacketPerm,fusionSignedPacketPerm,ite_true, if_true,sourceProbePacket,_root_.mul_one] using h

lemma classMap_sourceArtinAction (g:Artin M) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (aw g x)=bw g (classMap Q x) := by
  let H:Subgroup (Artin M):=
    { carrier:={g|∀x,classMap Q (aw g x)=bw g (classMap Q x)}
      one_mem':=by intro x; simp
      mul_mem':=by
        intro a b ha hb x
        simp only [map_mul,Equiv.Perm.mul_apply]
        exact (ha (aw b x)).trans (congrArg (bw a) (hb x))
      inv_mem':=by
        intro a ha x
        apply (bw a).injective
        have h:=ha (aw a⁻¹ x)
        simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h.symm }
  have hg:g∈H:=PresentedGroup.generated_by (braidRelators M) H (by
    intro s
    change ∀x,classMap Q (aw (generator M s) x)=bw (generator M s) (classMap Q x)
    intro x
    rw [sourceProbeAction_generator]
    exact classMap_sourcePacket M s x) g
  exact hg x

lemma sourceProbeAction_hom_reading (g:Artin M) (x:FiniteHomotopyClass Q (K:=K))
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (bw g⁻¹ (initialClass R (.inr (α,b)))) (classMap Q x)=
      classGeneratorArray Q (aw g x) ⟨α,n,v-1⟩ := by
  have hd : classHomDimension R n v (initialClass R (.inr (α,b)))
      (classMap Q (aw g x))=classGeneratorArray Q (aw g x) ⟨α,n,v-1⟩ :=
    classHom_dimension_flexible Q (aw g x) α b n v
  rw [← hd,classMap_sourceArtinAction]
  simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using
    (sourceProbeAction_homDimension M g
      (bw g⁻¹ (initialClass R (.inr (α,b)))) (classMap Q x) n v).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_QuotientFinrankKer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

lemma quotient_finrank_le_of_ker_le {K U W:Type*} [Field K]
    [AddCommGroup U] [Module K U] [Module.Finite K U]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (B:Submodule K U) (f:U→ₗ[K]W) (h:LinearMap.ker f≤B) :
    Module.finrank K (U ⧸ B)≤Module.finrank K W := by
  have hq:=B.finrank_quotient_add_finrank
  have hr:=f.finrank_range_add_finrank_ker
  have hk:=Submodule.finrank_mono h
  have hi:=Submodule.finrank_le (LinearMap.range f)
  omega

namespace ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J I' J':Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

omit [DecidableEq A] in
lemma homDimension_le_of_cycle_map
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (E':BasedComplex Q (K:=K) I') (F':BasedComplex Q (K:=K) J') (n v:ℤ)
    (T:homCycles Q E F n v→ₗ[K]homCycles Q E' F' n v)
    (hr:∀ f:homCycles Q E F n v,
      (T f).val∈homBoundaries Q E' F' n v→f.val∈homBoundaries Q E F n v) :
    homDimension Q E F n v≤homDimension Q E' F' n v := by
  let B:Submodule K (homCycles Q E F n v):=
    (homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype
  let B':Submodule K (homCycles Q E' F' n v):=
    (homBoundaries Q E' F' n v).comap (homCycles Q E' F' n v).subtype
  apply quotient_finrank_le_of_ker_le B (B'.mkQ.comp T)
  intro f hf
  exact hr f ((Submodule.Quotient.mk_eq_zero B').mp hf)

omit [DecidableEq A] in
theorem middleLayer_homDimension_le
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k n v:ℤ) (h:n+v=k-l+1) :
    homDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v≤homDimension Q E F n v := by
  let T:homCycles Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v→ₗ[K]
      homCycles Q E F n v :=
    (extendLayer Q E F l k).restrict (fun f hf=>
      extendLayer_cycle Q E F hE hF l k n v hf
        (pure_homSpace_linear Q _ _ (fun i=>i.property) (fun j=>j.property) h hf.1))
  apply homDimension_le_of_cycle_map Q _ _ E F n v T
  intro f hf
  exact layer_boundary_of_extended_boundary Q E F hE hF l k n v
    (pure_homSpace_linear Q _ _ (fun i=>i.property) (fun j=>j.property) h f.property.1) hf

omit [DecidableEq A] in
lemma middleLayer_totalHomDimension_le
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k:ℤ) :
    totalHomDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) (k-l+1)≤
      totalHomDimension Q E F (k-l+1) := by
  classical
  let M:=E.pureLayer Q hE l
  let N:=F.pureLayer Q hF k
  let D:=homInternalSupport Q M N ∪ homInternalSupport Q E F
  rw [totalHomDimension_eq_sum_of_subset Q M N (k-l+1) D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E F (k-l+1) D Finset.subset_union_right]
  exact Finset.sum_le_sum (fun v _=>middleLayer_homDimension_le Q E F hE hF l k _ v (by omega))

end ReversibleQuiver.Zigzag.BasedComplex
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbeActionEmbeddedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=K)
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeAction_embedded_hom_reading {I:Type} [Fintype I]
    (g:Artin M) (E:BasedComplex Q (K:=K) I)
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (n v:ℤ) :
    homDimension R
      (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex
      (complex Q E) n v=
      classGeneratorArray Q (aw g (classOfComplex Q E)) ⟨α,n,v-1⟩ := by
  change classHomDimension R n v
    (classOfComplex R (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex)
    (classOfComplex R (complex Q E))=_
  rw [← classMap_complex]
  have hy : classOfComplex R (minimalClassModel R
      (bw g⁻¹ (initialClass R (.inr (α,b))))).complex =
      bw g⁻¹ (initialClass R (.inr (α,b))) := minimalClassModel_class R _
  rw [hy,sourceProbeAction_hom_reading]

lemma sourceProbeAction_embedded_total_reading {I:Type} [Fintype I]
    (g:Artin M) (E:BasedComplex Q (K:=K) I)
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (t:ℤ) :
    totalHomDimension R
      (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex
      (complex Q E) t=
      classLevelArray Q (aw g (classOfComplex Q E)) (α,t-1) := by
  apply totalHomDimension_of_reading
  exact sourceProbeAction_embedded_hom_reading M g E α b

lemma sourceProbeAction_layer_middle_le {I:Type} [Fintype I]
    (g:Artin M) (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (l q:ℤ) :
    totalHomDimension R
      ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l)
      (complex Q (E.pureLayer Q hE q)) (q-l+1)≤
      classLevelArray Q (aw g (classOfComplex Q E)) (α,q-l) := by
  have h:=middleLayer_totalHomDimension_le R
    (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex
    (complex Q E) (minimalClassModel_minimal R _) (complex_minimal Q hE) l q
  rw [pureLayer_complex Q E hE q,sourceProbeAction_embedded_total_reading M g E α b] at h
  simp only [add_sub_cancel_right] at h
  exact h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ProbeConvexEuler
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "R" => probeQuiver Q
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "aw" => sourceArtinAction M (K:=ℂ)
local notation "bw" => sourceProbeAction M (K:=ℂ)

lemma sourceProbe_convex_euler
    (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (q:ℤ) (p:S⊕Unit→ℝ)
    (hconvex:(μ z s q-p)∈convexHull ℝ (Set.range (sourceConvexVector M J z s q)))
    (g:Artin M) (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hsoc:∀j:J,∀L c,coefficientSocle R
      ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥) :
    let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    -(generatorVector R N ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim (fusionFold m p) (fun _=>0)))≤
      ∑H,fusionWeight m H*(classLevelArray Q (aw g (O z s H)) (α,q-l):ℝ) := by
  dsimp only
  let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
    (minimalClassModel_minimal R _) l)
  let E:(S⊕Unit→ℝ)→ₗ[ℝ](ProbeVertex (FusionVertex (V:=S⊕Unit) m)→ℝ):=
    { toFun:=fun v=>Sum.elim (fusionFold m v) (fun _=>0)
      map_add':=by intro x y; funext v; cases v <;> simp [fusionFold,_root_.mul_add]
      map_smul':=by intro r x; funext v; cases v <;> simp [fusionFold,_root_.mul_left_comm] }
  let B:= (restrictedMatrix M J).Group
  let F:B→FusionLabel m→FiniteModel R (K:=ℂ):=fun w H=>
    FiniteModel.ofComplex R (complex Q (sourceConvexModel M J z s q w H).complex)
  let D:FusionLabel m→FiniteModel R (K:=ℂ):=fun H=>FiniteModel.ofComplex R (complex Q (Y z s H q))
  have hsum (w:B):(∑H,fusionWeight m H • generatorVector R (F w H).complex)=
      E (sourceConvexVector M J z s q w) := by
    change (∑H,fusionWeight m H • generatorVector R (complex Q (sourceConvexModel M J z s q w H).complex))=_
    simp_rw [generatorVector_complex]
    have hh:=sourceConvexModel_counts M J hJ z s q w
    funext v
    cases v with
    | inl v=>simpa [E,fusionOrbitWeightedVector] using congrFun hh v
    | inr v=>simp [E]
  have hD:(∑H,fusionWeight m H • generatorVector R (D H).complex)=E (μ z s q) := by
    change (∑H,fusionWeight m H • generatorVector R (complex Q (Y z s H q)))=_
    simp_rw [generatorVector_complex]
    have hh:=fusionOrbitWeightedVector_eq m d hd hdiag hm z s q
    funext v
    cases v with
    | inl v=>simpa [E,fusionOrbitWeightedVector] using congrFun hh v
    | inr v=>simp [E]
  have he:E (μ z s q-p)∈convexHull ℝ (Set.range (fun w=>∑H,fusionWeight m H • generatorVector R (F w H).complex)) := by
    have hh:E (μ z s q-p)∈E '' convexHull ℝ (Set.range (sourceConvexVector M J z s q)):=⟨_,hconvex,rfl⟩
    rw [E.image_convexHull,← Set.range_comp] at hh
    simpa only [hsum,Function.comp_def] using hh
  have hh:=family_subobject_middle_lower_bound R D N
    (fun H i=>i.property) (fun i=>i.property) F
    (fun w H i=>sourceConvexModel_pure M J hJ z s q w H i)
    (fun w H=>termwiseSplitInjection Q (sourceConvexActualInclusion M J hJ z s q w H))
    (Sum.inl '' Set.range (unfoldedInclusion M J))
    (fun w H i=>⟨_,sourceConvexModel_support M J z s q w H i,rfl⟩)
    (by
      rintro β ⟨γ,⟨⟨j,L⟩,rfl⟩,rfl⟩ c
      exact hsoc j L c)
    (fusionWeight m) (fun H=>(fusionWeight_pos m hm H).le) (E (μ z s q-p)) he
  rw [hD,map_sub,sub_sub_cancel_left] at hh
  simp only [mulVec_neg,dotProduct_neg] at hh
  refine hh.trans ?_
  apply Finset.sum_le_sum
  intro H hH
  apply mul_le_mul_of_nonneg_left _ (fusionWeight_pos m hm H).le
  have hi:=sourceProbeAction_layer_middle_le M g (minimalClassModel Q (O z s H)).complex
    (minimalClassModel_minimal Q _) α b l q
  have hx:classOfComplex Q (minimalClassModel Q (O z s H)).complex=O z s H:=minimalClassModel_class Q _
  have hid : (minimalClassModel Q (O z s H)).decidableEq =
      Classical.decEq (minimalClassModel Q (O z s H)).Index := Subsingleton.elim _ _
  rw [hid] at hx
  have heq:=congrArg (fun x:FiniteHomotopyClass Q (K:=ℂ)=>classLevelArray Q (aw g x) (α,q-l)) hx
  have hfin:=hi.trans_eq heq
  exact_mod_cast hfin

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FrameFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceMultiplicity_word (w:List (S×Bool)) (k:ℤ) :
    sourceMultiplicity M (sourceSignedWord M w) k=sourcePacketMultiplicity M w k := by
  unfold sourceMultiplicity
  rw [sourceFrameFamily_word,fusionFamilyMultiplicity_orbit]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ProbeCartanCore
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
open Zigzag Zigzag.BasedComplex _root_.Matrix

variable {V A:Type*} (Q:ReversibleQuiver V A) [Fintype V]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

omit [Fintype V] in
lemma probeCartan_core (α β:V) : unfoldedCartan R (.inl α) (.inl β)=unfoldedCartan Q α β := by
  unfold unfoldedCartan
  simp only [Sum.inl.injEq]
  congr 2
  apply Nat.card_congr
  refine {
    toFun:=?_
    invFun:=fun a=>⟨.inl a.val,congrArg Sum.inl a.property.1,congrArg Sum.inl a.property.2⟩
    left_inv:=?_
    right_inv:=?_ }
  · rintro ⟨a,ha⟩
    cases a with
    | inl a=>exact ⟨a,Sum.inl.inj ha.1,Sum.inl.inj ha.2⟩
    | inr p=>
      rcases p with ⟨v,b,c⟩
      cases c
      · exact False.elim (Sum.inr_ne_inl ha.2)
      · exact False.elim (Sum.inr_ne_inl ha.1)
  · rintro ⟨a,ha⟩
    cases a with
    | inl a=>rfl
    | inr p=>
      rcases p with ⟨v,b,c⟩
      cases c
      · exact False.elim (Sum.inr_ne_inl ha.2)
      · exact False.elim (Sum.inr_ne_inl ha.1)
  · intro a; rfl

omit [Fintype V] in
lemma probeCartan_leaf_core (α β:V) (b:Bool) :
    unfoldedCartan R (.inr (α,b)) (.inl β)=if α=β then -1 else 0 := by
  unfold unfoldedCartan
  simp only [Sum.inr_ne_inl,ite_false, if_false,zero_sub]
  have he : {a:ProbeArrow V A // (probeQuiver Q).source a=.inr (α,b) ∧ (probeQuiver Q).target a=.inl β} ≃
      {u:Unit // α=β} := {
    toFun:=fun a=>⟨(),by
      have hs:=(probe_source_iff Q α b a.val).mp a.property.1
      have ht:=a.property.2
      rw [hs] at ht
      exact Sum.inl.inj ht⟩
    invFun:=fun a=>⟨.inr (α,b,true),rfl,congrArg Sum.inl a.property⟩
    left_inv:=by intro a; apply Subtype.ext; exact ((probe_source_iff Q α b a.val).mp a.property.1).symm
    right_inv:=by intro a; apply Subtype.ext; exact Subsingleton.elim _ _ }
  rw [Nat.card_congr he]
  by_cases h:α=β
  · simp [h]
  · simp [h]

lemma probeCartan_mul_core (p:V→ℝ) (α:V) :
    (unfoldedCartan R *ᵥ Sum.elim p (fun _=>0)) (.inl α)=(unfoldedCartan Q *ᵥ p) α := by
  simp only [mulVec,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,probeCartan_core]

lemma probeCartan_mul_leaf (p:V→ℝ) (α:V) (b:Bool) :
    (unfoldedCartan R *ᵥ Sum.elim p (fun _=>0)) (.inr (α,b))= -p α := by
  simp only [mulVec,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,probeCartan_leaf_core]
  simp

lemma probeCartan_pairing (n:ProbeVertex V→ℝ) (p:V→ℝ) :
    n ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim p (fun _=>0))=
      (fun α=>n (.inl α)) ⬝ᵥ (unfoldedCartan Q *ᵥ p)-
        ∑ α,∑ b:Bool,n (.inr (α,b))*p α := by
  simp only [dotProduct,Fintype.sum_sum_type,probeCartan_mul_core]
  conv_lhs => rhs; arg 2; ext a; rw [probeCartan_mul_leaf]
  simp only [mul_neg,Finset.sum_neg_distrib,Fintype.sum_prod_type,sub_eq_add_neg]

end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbeActionLevelExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeAction_level_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass R (K:=K)) (α:ProbeVertex (FusionVertex (V:=S⊕Unit) m))
    (hp:∀s∈J,∀L,Sum.inl (Sum.inl s,L)≠α) (l:ℤ) :
    classLevelArray R (bw g x) (α,l)=classLevelArray R x (α,l) := by
  apply finsupp_mapDomain_fiber
  intro p he
  apply sourceProbeAction_exterior M J g hg
  intro s hs L hh
  apply hp s hs L
  exact hh.trans (congrArg Prod.fst he)

lemma sourceProbeOrbit_leaf_level (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α β:FusionVertex (V:=S⊕Unit) m) (b c:Bool) (l:ℤ) :
    classLevelArray R (bw g (initialClass R (.inr (α,b)))) (.inr (β,c),l)=
      if (α,b)=(β,c) ∧ l=0 then 1 else 0 := by
  rw [sourceProbeAction_level_exterior M J g hg _ _ (by intros; exact Sum.inl_ne_inr),
    classLevelArray_initial]
  simp only [Sum.inr.injEq]

lemma sourceProbeOrbit_leaf_vector (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α β:FusionVertex (V:=S⊕Unit) m) (b c:Bool) (l:ℤ) :
    generatorVector R
      ((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inr (β,c))=
      if (α,b)=(β,c) ∧ l=0 then 1 else 0 := by
  rw [generatorVector_minimalLayer,sourceProbeOrbit_leaf_level M J g hg]
  split <;> norm_num

lemma sourceProbeOrbit_cartan (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) (p:S⊕Unit→ℝ) :
    let Y:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l)
    generatorVector R Y ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim (fusionFold m p) (fun _=>0))=
      (fun β=>generatorVector R Y (.inl β)) ⬝ᵥ
        fusionFold m (fusionFoldedCartan m d *ᵥ p)-
      if l=0 then fusionWeight m α.2*p α.1 else 0 := by
  dsimp only
  let Y:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
    (minimalClassModel_minimal R _) l)
  have hpc:=probeCartan_pairing Q (generatorVector R Y) (fusionFold m p)
  have hpc' : generatorVector R Y ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim (fusionFold m p) (fun _=>0))=
      (fun β=>generatorVector R Y (.inl β)) ⬝ᵥ (unfoldedCartan Q *ᵥ fusionFold m p)-
        ∑β,∑c:Bool,generatorVector R Y (.inr (β,c))*fusionFold m p β := by
    convert hpc using 1 <;> first | (with_reducible_and_instances rfl) | (congr 5 <;> exact Subsingleton.elim _ _)
  have hc:(unfoldedCartan Q *ᵥ fusionFold m p)=
      fusionFold m (fusionFoldedCartan m d *ᵥ p) := by
    rw [fusionQuiver_cartan]
    exact fusion_intertwining m (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e)) d p
  apply hpc'.trans
  have hc': (fun β=>generatorVector R Y (.inl β)) ⬝ᵥ (unfoldedCartan Q *ᵥ fusionFold m p)=
      (fun β=>generatorVector R Y (.inl β)) ⬝ᵥ fusionFold m (fusionFoldedCartan m d *ᵥ p) :=
    congrArg ((fun β=>generatorVector R Y (.inl β)) ⬝ᵥ ·) hc
  apply congrArg₂ (·-·) hc'
  dsimp only [Y]
  simp only [sourceProbeOrbit_leaf_vector M J g hg]
  by_cases hl:l=0
  · simp [hl,Prod.mk.injEq,ite_and,ite_mul,fusionFold]
  · simp [hl]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FrameFamilyWeightedLevel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

lemma sourceFrameFamily_weighted_level (z:Artin M) (q:ℤ)
    (α:FusionVertex (V:=S⊕Unit) m) :
    (∑H,fusionWeight m H*(classLevelArray Q (sourceFrameFamily M z H) (α,q):ℝ))=
      fusionWeight m α.2*sourceMultiplicity M z q α.1 := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M z
  rw [sourceMultiplicity_word,sourceFrameFamily_word]
  have h:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm (sourcePacketWord w) (.inr ()) q) α
  simpa only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    fusionOrbitLayer_generator,fusionFold,sourcePacketMultiplicity] using h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_GroupProbeEuler
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
local notation "Q" => fusionQuiver m d hd
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=ℂ)
local notation "bw" => sourceProbeAction M (K:=ℂ)
local notation "C" => fusionFoldedCartan m d

theorem sourceGroup_probe_euler_oai
    (J T:Set S) (hJ:IsSpherical M J) (z g:Artin M) (hg:g∈artinParabolic M T)
    (q:ℤ) (p:S⊕Unit→ℝ)
    (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀v,v∉Sum.inl '' J→sourceMultiplicity M z q v=p v)
    (huniv:∀a∈artinParabolic M J,
      (∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀j:J,p (.inl (j:S))≤ sourceMultiplicity M (a*z) q (.inl (j:S)))
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hsoc:∀j:J,∀L c,coefficientSocle R
      ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥) :
    let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    (if l=0 then fusionWeight m α.2*p α.1 else 0)-
      (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p) ≤
      fusionWeight m α.2*sourceMultiplicity M (g*z) (q-l) α.1 := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M z
  have hc:=source_convex_subobjects_full M J hJ (sourcePacketWord w) (.inr ()) q p
    (by simpa only [sourceFrameFamily_word] using hz) hp
    (by simpa only [sourceMultiplicity_word,sourcePacketMultiplicity] using hext)
    (by
      intro a ha hcap j
      have family_eq : sourceFrameFamily M (a*sourceSignedWord M w)=
          (fun L=>aw a (fusionPacketOrbit m d hd hdiag (sourcePacketWord w) (.inr ()) L)) := by
        funext label
        rw [sourceFrameFamily_mul,sourceFrameFamily_word]
      have translated_cap : ∀ label,
          ClassCapOn Q (sourceFrameFamily M (a*sourceSignedWord M w) label)
            (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q := by
        simpa only [family_eq] using hcap
      simpa only [sourceMultiplicity,family_eq] using huniv a ha translated_cap j)
  have hh:=sourceProbe_convex_euler M J hJ (sourcePacketWord w) (.inr ()) q p hc g α b l hsoc
  have hcart:=sourceProbeOrbit_cartan M (K:=ℂ) T g⁻¹ ((artinParabolic M T).inv_mem hg) α b l p
  dsimp only at hh hcart ⊢
  rw [hcart,neg_sub] at hh
  have hw:=sourceFrameFamily_weighted_level M (g*sourceSignedWord M w) (q-l) α
  simp only [sourceFrameFamily_mul,sourceFrameFamily_word] at hw
  exact hh.trans_eq hw

end HarmonicArtin

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.sourceGroup_probe_euler_oai := @OAI.HarmonicArtin.sourceGroup_probe_euler_oai
