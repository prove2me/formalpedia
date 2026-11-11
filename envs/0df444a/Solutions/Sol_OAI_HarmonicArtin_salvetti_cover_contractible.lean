-- Prove2me | solution 1 for OAI.HarmonicArtin.salvetti_cover_contractible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T18:08:22.300571+00:00
-- url     : https://prove2.me/submissions/273794a0-630c-4feb-be47-1f992e590cb9

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag015
import Theorems.Thm_OAI_HarmonicArtin_sourceEarlierLower_contractible

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveLiftSimple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

theorem finiteArtin_positive_fraction [Finite M.Group] (g:Artin M) :
    ∃ u v:List S,g=wordArtin M u*(wordArtin M v)⁻¹ := by
  obtain ⟨z,hz⟩:=exists_longest M.toCoxeterSystem
  obtain ⟨n,u,hu⟩:=positive_fraction_longest M z hz g
  obtain ⟨v,hv⟩:=positiveLift_longest_square_positive M z
  obtain ⟨v',hv'⟩:=wordArtin_positive_power M v n
  refine ⟨u,v',?_⟩
  rw [hu,hv',hv,zpow_neg,zpow_natCast]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator _root_.OAI.HarmonicArtin.sourceCosetProfile_apply _root_.OAI.HarmonicArtin.unfoldedHom_simple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

 theorem spherical_singleton (M : CoxeterMatrix S) (s : S) : IsSpherical M {s} := by
  have horder : IsOfFinOrder (M.simple s) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, M.toCoxeterSystem.simple_sq s⟩
  unfold IsSpherical coxeterParabolic
  rw [Set.image_singleton, ← Subgroup.zpowers_eq_closure]
  exact horder.finite_zpowers

 theorem rightCoset_empty (M : CoxeterMatrix S) (x : Artin M) :
    rightCoset M ∅ x = {x} := by
  ext g
  simp [rightCoset, artinParabolic, mul_inv_eq_one]

 theorem elementVertex_le (M : CoxeterMatrix S) (T : Set S) (hT : IsSpherical M T)
    (x g : Artin M) (hg : g * x⁻¹ ∈ artinParabolic M T) :
    cosetVertex M ∅ (spherical_empty M) g ≤ cosetVertex M T hT x := by
  change (∅ : Set S) ⊆ T ∧ rightCoset M ∅ g ⊆ rightCoset M T x
  refine ⟨Set.empty_subset T, ?_⟩
  rw [rightCoset_empty]
  exact Set.singleton_subset_iff.mpr hg

 theorem deligne_connected (M : CoxeterMatrix S) : CategoryTheory.IsConnected (Deligne M) := by
  apply CategoryTheory.IsConnected.of_induct (j₀ := cosetVertex M ∅ (spherical_empty M) 1)
  intro p hbase hmor P
  have hstep (s : S) (x : Artin M) :
      cosetVertex M ∅ (spherical_empty M) x ∈ p ↔
        cosetVertex M ∅ (spherical_empty M) (generator M s * x) ∈ p := by
    have hx : x * x⁻¹ ∈ artinParabolic M {s} := by simp
    have hs : (generator M s * x) * x⁻¹ ∈ artinParabolic M {s} := by
      simp only [mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.subset_closure (Set.mem_image_of_mem _ (Set.mem_singleton s))
    exact (hmor (CategoryTheory.homOfLE
      (elementVertex_le M {s} (spherical_singleton M s) x x hx))).trans
      (hmor (CategoryTheory.homOfLE
        (elementVertex_le M {s} (spherical_singleton M s) x (generator M s * x) hs))).symm
  have hall (x : Artin M) : cosetVertex M ∅ (spherical_empty M) x ∈ p := by
    have hgen : Subgroup.closure (Set.range (generator M)) = ⊤ :=
      PresentedGroup.closure_range_of (braidRelators M)
    have hx : x ∈ Subgroup.closure (Set.range (generator M)) := by rw [hgen]; trivial
    induction hx using Subgroup.closure_induction_left with
    | one => exact hbase
    | mul_left g hg y _ hy =>
      rcases hg with ⟨s, rfl⟩
      exact (hstep s y).mp hy
    | inv_mul_cancel g hg y _ hy =>
      rcases hg with ⟨s, rfl⟩
      apply (hstep s ((generator M s)⁻¹ * y)).mpr
      simpa only [mul_inv_cancel_left] using hy
  rcases P with ⟨⟨T, C⟩, hT, x, hx⟩
  change C = rightCoset M T x at hx
  subst C
  exact (hmor (CategoryTheory.homOfLE
    (elementVertex_le M T hT x x (by simp)))).mp (hall x)

open _root_.Matrix

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_MaximalReducedMonoidPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveDegree_generator _root_.OAI.HarmonicArtin.positiveDegree_mul _root_.OAI.HarmonicArtin.positiveDegree_one _root_.OAI.HarmonicArtin.positiveDegree_word _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_involutive _root_.OAI.HarmonicArtin.positiveReverse_one _root_.OAI.HarmonicArtin.positiveSimpleLift_one _root_.OAI.HarmonicArtin.positiveSimpleLift_simple _root_.OAI.HarmonicArtin.positiveToCoxeter_generator _root_.OAI.HarmonicArtin.positiveToCoxeter_simpleLift _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma maximal_reduced_monoid_prefix (s:S) (w:List S) :
    ∃ u v:List S, M.toCoxeterSystem.IsReduced u ∧
      wordPositive M (s::w)=wordPositive M u*wordPositive M v ∧
      u.length+v.length=(s::w).length ∧ 0<u.length ∧
      ∀ u' v':List S,M.toCoxeterSystem.IsReduced u'→
        wordPositive M (s::w)=wordPositive M u'*wordPositive M v'→
        u'.length+v'.length=(s::w).length→u'.length≤u.length := by
  let P:ℕ→Prop:=fun n=>∃u v:List S,M.toCoxeterSystem.IsReduced u ∧
    wordPositive M (s::w)=wordPositive M u*wordPositive M v ∧
    u.length+v.length=(s::w).length ∧ u.length=n
  have hP:P 1 := by
    refine ⟨[s],w,?_,?_,by simp [Nat.add_comm],rfl⟩
    · change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
      exact M.toCoxeterSystem.length_simple s
    · simp [wordPositive]
  have hb:1≤(s::w).length:=by simp
  obtain ⟨u,v,hu,he,hl,hmax⟩:=Nat.findGreatest_spec hb hP
  refine ⟨u,v,hu,he,hl,?_,?_⟩
  · have hh:=Nat.le_findGreatest hb hP
    omega
  · intro u' v' hu' he' hl'
    rw [hmax]
    exact Nat.le_findGreatest (by omega) ⟨u',v',hu',he',hl',rfl⟩

lemma reduced_monoid_left_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (s::w)) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordPositive M w=positiveGenerator M s*wordPositive M v ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsLeftDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.simple s*cs.wordProd w)=w.length+1
    rw [cs.not_isLeftDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.simple s*cs.wordProd w)
  have hp:cs.wordProd (s::v)=cs.wordProd w := by
    rw [cs.wordProd_cons,←he,cs.simple_mul_simple_cancel_left]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isLeftDescent_iff.mp hd
  have hr:cs.IsReduced (s::v) := by
    change cs.length (cs.wordProd (s::v))=v.length+1
    rw [hp,hw.eq,hl]
  refine ⟨v,hv,?_,hl⟩
  exact wordPositive_eq_of_reduced M w (s::v) hw hr hp.symm

lemma reduced_monoid_right_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (w++[s])) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordPositive M w=wordPositive M v*positiveGenerator M s ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsRightDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.wordProd (w++[s]))=(w++[s]).length
    simp only [cs.wordProd_append,cs.wordProd_cons,cs.wordProd_nil,mul_one,List.length_append,List.length_singleton]
    rw [cs.not_isRightDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.wordProd w*cs.simple s)
  have hp:cs.wordProd (v++[s])=cs.wordProd w := by
    simp only [cs.wordProd_append,cs.wordProd_cons,cs.wordProd_nil,mul_one]
    rw [←he,mul_assoc,cs.simple_mul_simple_self,mul_one]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isRightDescent_iff.mp hd
  have hr:cs.IsReduced (v++[s]) := by
    change cs.length (cs.wordProd (v++[s]))=(v++[s]).length
    rw [hp,hw.eq,List.length_append,List.length_singleton,hl]
  refine ⟨v,hv,?_,hl⟩
  have heq:=wordPositive_eq_of_reduced M w (v++[s]) hw hr hp.symm
  rw [wordPositive_append] at heq
  simpa only [wordPositive,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using heq

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePositiveWordPositive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma probePositiveWord_eq_of_positive (J:Set S) (u v:List J)
    (h:wordPositive (restrictedMatrix M J) u=wordPositive (restrictedMatrix M J) v)
    (x:FiniteHomotopyClass R (K:=K)) : probePositiveWord M J u x=probePositiveWord M J v x := by
  apply probePositiveWord_eq_of_restricted M J u v
  have he:=congrArg (positiveToArtin (restrictedMatrix M J)) h
  simpa only [positiveToArtin_word] using he

theorem probe_positive_monoid_top_factor (J:Set S) (hJ:IsSpherical M J)
    (x:FiniteHomotopyClass R (K:=K)) (t:ℤ)
    (hx:ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t)
    (w:List J) (j:J) (ℓ:ℤ) (hlt:t<ℓ)
    (hy:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) ℓ)
    (L:FusionLabel m) (c:ℤ)
    (htop:¬ClassTestExact R (probeCoreInclusion M J (j,L)) ℓ c (probePositiveWord M J w x)) :
    ∃v:List J,wordPositive (restrictedMatrix M J) w=
      positiveGenerator (restrictedMatrix M J) j*wordPositive (restrictedMatrix M J) v ∧ v.length+1=w.length := by
  let N:=restrictedMatrix M J
  let U:=Set.range (probeCoreInclusion M J)
  induction w using (measure (fun w:List J=>w.length)).wf.induction generalizing j ℓ L c with
  | h w ih=>
    cases w with
    | nil=>exact (htop (hx _ ⟨(j,L),rfl⟩ ℓ hlt c)).elim
    | cons s w=>
      obtain ⟨u,v,hu,he,hlen,hpos,hmax⟩:=maximal_reduced_monoid_prefix N s w
      have heword:wordPositive N (s::w)=wordPositive N (u++v) := by
        rw [wordPositive_append]; exact he
      have heact:probePositiveWord M J (s::w) x=
          probePositiveWord M J u (probePositiveWord M J v x) := by
        rw [probePositiveWord_eq_of_positive M J _ _ heword,probePositiveWord_append]
      have hvsmall:v.length<(s::w).length:=by omega
      let y:=probePositiveWord M J v x
      have hcap:ClassTestUpper R y U ℓ := by
        apply probePositiveWord_testUpper_reflect M J u
        rw [←heact]
        exact hy
      by_cases hj:N.toCoxeterSystem.IsReduced (j::u)
      · have hncap:¬ClassTestUpper R y U (ℓ-1) := by
          intro hc
          apply htop
          rw [heact]
          exact probe_reduced_ascent_top_exact M J hJ u j hu hj y (ℓ-1) ℓ (by omega) hc
            (by rw [←heact]; exact hy) L c
        have htopv:∃γ:J,∃L' c',¬ClassTestExact R (probeCoreInclusion M J (γ,L')) ℓ c' y := by
          by_contra hh
          apply hncap
          intro α hα l hl c'
          obtain ⟨⟨γ,L'⟩,rfl⟩:=hα
          by_cases heq:l=ℓ
          · subst l
            by_contra hnot
            exact hh ⟨γ,L',c',hnot⟩
          · exact hcap _ ⟨(γ,L'),rfl⟩ l (by omega) c'
        obtain ⟨γ,L',c',hγ⟩:=htopv
        obtain ⟨v',hv',hvlen⟩:=ih v hvsmall γ ℓ hlt hcap L' c' hγ
        have huγ:N.toCoxeterSystem.IsReduced (u++[γ]) := by
          by_contra hnot
          obtain ⟨u',_,he',_⟩:=reduced_monoid_right_factor N u γ hu hnot
          have hea:probePositiveWord M J u y=
              probePositiveWord M J u' (sourceProbePacket M γ y) := by
            have hw:wordPositive N u=wordPositive N (u'++[γ]):=by
              rw [wordPositive_append]; exact he'
            rw [probePositiveWord_eq_of_positive M J _ _ hw,probePositiveWord_append]
            rfl
          have hγcap:ClassTestUpper R (sourceProbePacket M γ y) U ℓ := by
            apply probePositiveWord_testUpper_reflect M J u'
            rw [←hea,←heact]
            exact hy
          exact hγ (sourceProbePacket_top_exact_of_cap M J γ y hγcap L' c')
        have hext:wordPositive N (s::w)=wordPositive N (u++[γ])*wordPositive N v' := by
          rw [he,hv',wordPositive_append]
          exact (_root_.mul_assoc _ _ _).symm
        have hlxt:(u++[γ]).length+v'.length=(s::w).length := by
          simp only [List.length_append,List.length_singleton]
          omega
        have hh:=hmax (u++[γ]) v' huγ hext hlxt
        simp only [List.length_append,List.length_singleton] at hh
        omega
      · obtain ⟨u',_,he',hlen'⟩:=reduced_monoid_left_factor N u j hu hj
        refine ⟨u'++v,?_,?_⟩
        · rw [he,he',wordPositive_append,_root_.mul_assoc]
        · simp only [List.length_append]
          omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePositiveWordMonoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.positiveDegree_generator _root_.OAI.HarmonicArtin.positiveDegree_mul _root_.OAI.HarmonicArtin.positiveDegree_one _root_.OAI.HarmonicArtin.positiveDegree_word _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_involutive _root_.OAI.HarmonicArtin.positiveReverse_one _root_.OAI.HarmonicArtin.positiveSimpleLift_one _root_.OAI.HarmonicArtin.positiveSimpleLift_simple _root_.OAI.HarmonicArtin.positiveToCoxeter_generator _root_.OAI.HarmonicArtin.positiveToCoxeter_simpleLift _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M

lemma probePositiveWord_monoid_factor (T:Set S) (w v:List T) (j:T)
    (he:wordPositive (restrictedMatrix M T) w=
      positiveGenerator (restrictedMatrix M T) j*wordPositive (restrictedMatrix M T) v)
    (x:FiniteHomotopyClass (probeQuiver (fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M))) (K:=K)) :
    probePositiveWord M T w x=sourceProbePacket M j (probePositiveWord M T v x) := by
  have hw:wordPositive (restrictedMatrix M T) w=wordPositive (restrictedMatrix M T) (j::v):=he
  rw [probePositiveWord_eq_of_positive M T w (j::v) hw,probePositiveWord_cons]

theorem positive_monoid_eq_of_probe_eq (T:Set S) (hT:IsSpherical M T) (a b:List T)
    (he:∀s:T,∀L d,probePositiveWord M T a (sourceInitialProbe M (K:=K) s L d)=
        probePositiveWord M T b (sourceInitialProbe M (K:=K) s L d)) :
    wordPositive (restrictedMatrix M T) a=wordPositive (restrictedMatrix M T) b := by
  induction a using (measure (fun a:List T=>a.length)).wf.induction generalizing b with
  | h a ih=>
    cases a with
    | nil=>
      have hb:b=[]:=by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro s hs
        let L:FusionLabel m:=fun e=>⟨0,by have :=fusionLabelSize_ge_four M e;omega⟩
        have hc:ClassTestUpper _ (probePositiveWord M T [] (sourceInitialProbe M (K:=K) s L false))
            (Set.range (probeCoreInclusion M T)) 1:=by
          exact (probePositiveWord_initial_cap_iff M T [] s L false).mpr (by simp)
        rw [he s L false] at hc
        exact probePositiveWord_initial_cap_not_mem M T b s L false hc hs
      rw [hb]
    | cons s a=>
      let L:FusionLabel m:=fun e=>⟨0,by have :=fusionLabelSize_ge_four M e;omega⟩
      let x:=sourceInitialProbe M (K:=K) s L false
      obtain ⟨l,hl,hcap,j,H,c,htop⟩:=probePositiveWord_initial_top M T (s::a) s (by simp) L false (K:=K)
      have hx:=sourceInitialProbe_cap M (K:=K) T s L false
      obtain ⟨a',ha',halen⟩:=probe_positive_monoid_top_factor M T hT x 1 hx (s::a) j l hl hcap H c htop
      rw [he s L false] at hcap htop
      obtain ⟨b',hb',hblen⟩:=probe_positive_monoid_top_factor M T hT x 1 hx b j l hl hcap H c htop
      have he':∀s:T,∀L d,probePositiveWord M T a' (sourceInitialProbe M (K:=K) s L d)=
          probePositiveWord M T b' (sourceInitialProbe M (K:=K) s L d):=by
        intro t L d
        apply (sourceProbePacket M j).injective
        rw [←probePositiveWord_monoid_factor M T (s::a) a' j ha',←probePositiveWord_monoid_factor M T b b' j hb']
        exact he t L d
      have hi:=ih a' (show a'.length<(s::a).length by omega) b' he'
      rw [ha',hb',hi]

theorem spherical_positive_words_reflect (T:Set S) (hT:IsSpherical M T) (a b:List T)
    (he:wordArtin M (a.map Subtype.val)=wordArtin M (b.map Subtype.val)) :
    wordPositive (restrictedMatrix M T) a=wordPositive (restrictedMatrix M T) b := by
  apply positive_monoid_eq_of_probe_eq (K:=ℚ) M T hT a b
  intro s L d
  simp only [probePositiveWord,he]

theorem spherical_positiveToAmbient_injective (T:Set S) (hT:IsSpherical M T) :
    Function.Injective ((restrictedArtinHom M T).comp (positiveToArtin (restrictedMatrix M T))) := by
  intro a b hab
  obtain ⟨u,rfl⟩:=PresentedMonoid.surjective_mk a
  obtain ⟨v,rfl⟩:=PresentedMonoid.surjective_mk b
  have ha:PresentedMonoid.mk (positiveBraidRelations (restrictedMatrix M T)) u=
      wordPositive (restrictedMatrix M T) (FreeMonoid.toList u):=by rw [wordPositive_mk,FreeMonoid.ofList_toList]
  have hb:PresentedMonoid.mk (positiveBraidRelations (restrictedMatrix M T)) v=
      wordPositive (restrictedMatrix M T) (FreeMonoid.toList v):=by rw [wordPositive_mk,FreeMonoid.ofList_toList]
  rw [ha,hb] at hab ⊢
  apply spherical_positive_words_reflect M T hT
  simpa only [MonoidHom.comp_apply,positiveToArtin_word,restrictedArtinHom_word] using hab

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Cancellation_SphericalPositiveCancelMonoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem spherical_positiveToArtin_injective (T:Set S) (hT:IsSpherical M T) :
    Function.Injective (positiveToArtin (restrictedMatrix M T)) := by
  intro a b h
  apply spherical_positiveToAmbient_injective M T hT
  exact congrArg (restrictedArtinHom M T) h

omit [LinearOrder S] in
theorem spherical_positive_monoid_fractions (T:Set S) (hT:IsSpherical M T)
    (g:Artin (restrictedMatrix M T)) :
    (∃a b:PositiveArtin (restrictedMatrix M T),g=positiveToArtin _ a*(positiveToArtin _ b)⁻¹) ∧
    (∃c d:PositiveArtin (restrictedMatrix M T),g=(positiveToArtin _ c)⁻¹*positiveToArtin _ d) := by
  have : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  constructor
  · obtain ⟨a,b,h⟩:=finiteArtin_positive_fraction (restrictedMatrix M T) g
    exact ⟨wordPositive _ a,wordPositive _ b,by simpa only [positiveToArtin_word] using h⟩
  · obtain ⟨a,b,h⟩:=finiteArtin_positive_left_fraction (restrictedMatrix M T) g
    exact ⟨wordPositive _ a,wordPositive _ b,by simpa only [positiveToArtin_word] using h⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_ParabolicLongest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.restrictedArtinHom_generator _root_.OAI.HarmonicArtin.unfoldedHom_simple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma parabolic_longest_complement_minimum (R T:Set S) (hRT:R⊆T)
    (zR zT:M.Group) (hR:IsParabolicLongest M R zR) (hT:IsParabolicLongest M T zT) :
    ∀v:coxeterParabolic M R,
      M.toCoxeterSystem.length (zT*zR⁻¹)≤M.toCoxeterSystem.length (zT*zR⁻¹*v) := by
  intro v
  have hRm: zR⁻¹∈coxeterParabolic M R:=(coxeterParabolic M R).inv_mem hR.1
  have hTm: zR⁻¹∈coxeterParabolic M T:=coxeterParabolic_mono M hRT hRm
  have hl:=parabolic_longest_length_mul M T zT hT zR⁻¹ hTm
  have hm: zR⁻¹*v∈coxeterParabolic M R:=(coxeterParabolic M R).mul_mem hRm v.property
  have hl':=parabolic_longest_length_mul M T zT hT (zR⁻¹*v) (coxeterParabolic_mono M hRT hm)
  have hb:=hR.2 _ hm
  rw [M.toCoxeterSystem.length_inv] at hl
  rw [←mul_assoc] at hl'
  omega

theorem lifted_top_face (R T:Set S) (hRs:IsSpherical M R) (hTs:IsSpherical M T) (hRT:R⊆T)
    (zR zT:M.Group) (hR:IsParabolicLongest M R zR) (hT:IsParabolicLongest M T zT)
    (a:Artin M) :
    LiftedFace M (a*positiveLift M zT*(positiveLift M zR)⁻¹,⟨R,hRs⟩) (a,⟨T,hTs⟩) := by
  let p:=zT*zR⁻¹
  have hp:p∈coxeterParabolic M T:=(coxeterParabolic M T).mul_mem hT.1
    (coxeterParabolic_mono M hRT ((coxeterParabolic M R).inv_mem hR.1))
  obtain ⟨u,hu,hr,he⟩:=(mem_parabolic_iff_reduced_word M.toCoxeterSystem T p).mp hp
  change wordCoxeter M u=p at he
  have hlen:M.toCoxeterSystem.length (p*zR)=M.toCoxeterSystem.length p+M.toCoxeterSystem.length zR:=by
    have hh:=parabolic_longest_length_mul M T zT hT zR⁻¹
      (coxeterParabolic_mono M hRT ((coxeterParabolic M R).inv_mem hR.1))
    simp only [M.toCoxeterSystem.length_inv] at hh
    dsimp [p]
    rw [inv_mul_cancel_right]
    exact hh.symm
  have hpos:positiveLift M zT=positiveLift M p*positiveLift M zR:=by
    simpa only [p,inv_mul_cancel_right] using positiveLift_mul M p zR hlen
  refine ⟨hRT,u,hu,hr.eq,?_,?_⟩
  · rw [he]
    exact parabolic_longest_complement_minimum M R T hRT zR zT hR hT
  · change a*positiveLift M zT*(positiveLift M zR)⁻¹=a*wordArtin M u
    rw [hpos,←he,positiveLift_word M u hr]
    group

theorem lifted_same_top_le (R T:Set S) (hRs:IsSpherical M R) (hTs:IsSpherical M T) (hRT:R⊆T)
    (zR zT:M.Group) (hR:IsParabolicLongest M R zR) (hT:IsParabolicLongest M T zT)
    (b:Artin M) :
    (b*(positiveLift M zR)⁻¹,⟨R,hRs⟩)≤
      ((b*(positiveLift M zT)⁻¹,⟨T,hTs⟩):LiftedCell M) := by
  apply (lifted_le_iff_face M _ _).mpr
  have h:=lifted_top_face M R T hRs hTs hRT zR zT hR hT (b*(positiveLift M zT)⁻¹)
  simpa only [mul_assoc,inv_mul_cancel_left] using h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TieCode
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceTieCode_injective : Function.Injective (sourceTieCode M) := by
  let :=sourceDeligne_countable M
  let :=Encodable.ofCountable (Deligne M)
  exact Encodable.encode_injective

lemma sourceVertexKey_injective : Function.Injective (sourceVertexKey M) := by
  intro P R h
  apply sourceTieCode_injective M
  exact congrArg (fun k:Lex (Colex (ℕ→₀ℕ) × ℕ)=>(ofLex k).2) h

theorem sourceEarlier_wellFounded : WellFounded (SourceEarlier M) :=
  InvImage.wf (sourceVertexKey M) wellFounded_lt

lemma sourceEarlier_trichotomy (P R:Deligne M) :
    SourceEarlier M P R ∨ P=R ∨ SourceEarlier M R P := by
  rcases lt_trichotomy (sourceVertexKey M P) (sourceVertexKey M R) with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (sourceVertexKey_injective M h))
  · exact Or.inr (Or.inr h)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlierUpper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceUpperClip_le {P R:Deligne M} (h:P≤ R) : sourceUpperClip M P R≤ R := by
  have he:=sourceCoset_eq M R _ (h.2 (sourceCosetRepresentative_mem M P))
  rw [←he]
  exact sourceCoset_le M Set.inter_subset_left _

lemma sourceUpperClip_le_top (P R:Deligne M) : sourceUpperClip M P R≤ sourceActiveTop M P :=
  sourceCoset_le M Set.inter_subset_right _

lemma sourceUpperRetraction_le (P:Deligne M) (R:SourceEarlierUpper M P) :
    sourceUpperRetraction M P R≤ R := sourceUpperClip_le M R.property.1.le

lemma sourceUpperRetraction_le_center (P:Deligne M) (ha:(sourceActive M P).Nonempty)
    (R:SourceEarlierUpper M P) : sourceUpperRetraction M P R≤ sourceUpperCenter M P ha :=
  sourceUpperClip_le_top M P R

lemma sourceEarlierUpper_nonempty_iff (P:Deligne M) :
    Nonempty (SourceEarlierUpper M P) ↔ (sourceActive M P).Nonempty := by
  constructor
  · rintro ⟨R⟩
    obtain ⟨i,_,_,hi⟩:=sourceUpper_earlier_has_active M R.property.1 R.property.2
    exact ⟨i,hi⟩
  · intro h
    exact ⟨sourceUpperCenter M P h⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_RealizeSimplex
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section TopologyDependencies
open CategoryTheory Opposite Simplicial
open scoped unitInterval

namespace HarmonicArtin
universe u

variable (P : Type u) [Preorder P] [OrderBot P]

lemma prependNerve_face {n : SimplexCategory} (x : (nerve P).obj (op n)) :
    (nerve P).map (SimplexCategory.δ (0 : Fin (n.len + 2))).op (prependNerve P x) = x := by
  apply nerve.ext_of_isThin
  funext i
  rfl

@[simp] lemma nerveConeSimplex_zero {n : SimplexCategory}
    (x : (nerve P).obj (op n)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    nerveConeSimplex P x z 0 = realizeSimplex (nerve P) x z := by
  change realizeSimplex (nerve P) (prependNerve P x) (coneSimplex n.len (z, 0)) = _
  rw [coneSimplex_zero]
  have h := realizeSimplex_natural (nerve P)
    (SimplexCategory.δ (0 : Fin (n.len + 2))) (prependNerve P x) z
  rw [prependNerve_face] at h
  exact h.symm

lemma nerveCone_zero :
    (TopCat.ofHom (nerveCone P)) ≫ pathEvaluate P 0 = 𝟙 |nerve P| := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nerveCone, TopCat.ofHom_hom, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (toSimp _ n).injective
  ext z
  change toSimp _ n ((TopCat.toSSet.map (pathEvaluate P 0)).app n
      ((toSimp _ n).symm (nerveConeSimplex P x))) z = _
  rw [toSimp_map, Equiv.apply_symm_apply]
  exact nerveConeSimplex_zero P x z

lemma nerveCone_one :
    (TopCat.ofHom (nerveCone P)) ≫ pathEvaluate P 1 = TopCat.const (nerveBotPoint P) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nerveCone, TopCat.ofHom_hom, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (toSimp _ n).injective
  ext z
  change toSimp _ n ((TopCat.toSSet.map (pathEvaluate P 1)).app n
      ((toSimp _ n).symm (nerveConeSimplex P x))) z = _
  rw [toSimp_map, Equiv.apply_symm_apply]
  exact nerveConeSimplex_one P x z

theorem nerve_orderBot_contractible : ContractibleSpace |nerve P| := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨nerveBotPoint P, ⟨{
    toFun := fun p => nerveCone P p.2 p.1
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · exact (nerveCone P).uncurry.continuous.comp continuous_swap
  · intro x
    exact ConcreteCategory.congr_hom (nerveCone_zero P) x
  · intro x
    exact ConcreteCategory.congr_hom (nerveCone_one P) x

section TopCone
variable (Q : Type u) [Preorder Q] [OrderTop Q]

lemma appendNerve_face {n : SimplexCategory} (x : (nerve Q).obj (op n)) :
    (nerve Q).map (SimplexCategory.δ (Fin.last (n.len + 1))).op (appendNerve Q x) = x := by
  apply nerve.ext_of_isThin
  funext i
  change (Fin.snoc (α := fun _ : Fin (n.len + 2) => Q) x.obj ⊤)
    ((Fin.last (n.len + 1)).succAbove i) = x.obj i
  simp only [Fin.succAbove_last, Fin.snoc_castSucc]

@[simp] lemma nerveTopConeSimplex_zero {n : SimplexCategory}
    (x : (nerve Q).obj (op n)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    nerveTopConeSimplex Q x z 0 = realizeSimplex (nerve Q) x z := by
  change realizeSimplex (nerve Q) (appendNerve Q x) (topConeSimplex n.len (z, 0)) = _
  rw [topConeSimplex_zero]
  have h := realizeSimplex_natural (nerve Q)
    (SimplexCategory.δ (Fin.last (n.len + 1))) (appendNerve Q x) z
  rw [appendNerve_face] at h
  change realizeSimplex (nerve Q) x z =
    realizeSimplex (nerve Q) (appendNerve Q x)
      (Convexity.StdSimplex.map (Fin.last (n.len + 1)).succAbove z) at h
  rw [Fin.succAbove_last] at h
  exact h.symm

lemma nerveTopCone_zero :
    (TopCat.ofHom (nerveTopCone Q)) ≫ pathEvaluate Q 0 = 𝟙 |nerve Q| := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nerveTopCone, TopCat.ofHom_hom, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (toSimp _ n).injective
  ext z
  change toSimp _ n ((TopCat.toSSet.map (pathEvaluate Q 0)).app n
      ((toSimp _ n).symm (nerveTopConeSimplex Q x))) z = _
  rw [toSimp_map, Equiv.apply_symm_apply]
  exact nerveTopConeSimplex_zero Q x z

lemma nerveTopCone_one :
    (TopCat.ofHom (nerveTopCone Q)) ≫ pathEvaluate Q 1 = TopCat.const (nerveTopPoint Q) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nerveTopCone, TopCat.ofHom_hom, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (toSimp _ n).injective
  ext z
  change toSimp _ n ((TopCat.toSSet.map (pathEvaluate Q 1)).app n
      ((toSimp _ n).symm (nerveTopConeSimplex Q x))) z = _
  rw [toSimp_map, Equiv.apply_symm_apply]
  exact nerveTopConeSimplex_one Q x z

theorem nerve_orderTop_contractible : ContractibleSpace |nerve Q| := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨nerveTopPoint Q, ⟨{
    toFun := fun p => nerveTopCone Q p.2 p.1
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · exact (nerveTopCone Q).uncurry.continuous.comp continuous_swap
  · intro x
    exact ConcreteCategory.congr_hom (nerveTopCone_zero Q) x
  · intro x
    exact ConcreteCategory.congr_hom (nerveTopCone_one Q) x

end TopCone
end HarmonicArtin

end TopologyDependencies

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NerveOrderMap
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open scoped unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma simplex_zero_unique (z:Convexity.StdSimplex ℝ (Fin 1)) :
    z=Convexity.StdSimplex.single 0 :=
  Subsingleton.elim _ _

lemma realizeSimplex_const {P Q:Type u} [Preorder P] [Preorder Q] (c:Q)
    {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    realizeSimplex (nerve Q) ((nerveMap (OrderHom.const P c).toFunctor).app (op n) x) z=nerveVertex Q c := by
  let a:n⟶⦋0⦌:=SimplexCategory.mkHom (OrderHom.const _ 0)
  have he:(nerve Q).map a.op (ComposableArrows.mk₀ c)=
      (nerveMap (OrderHom.const P c).toFunctor).app (op n) x:=by
    apply nerve.ext_of_isThin
    rfl
  have hh:=realizeSimplex_natural (nerve Q) a (ComposableArrows.mk₀ c) z
  rw [he] at hh
  exact hh.trans (congrArg (realizeSimplex (nerve Q) (ComposableArrows.mk₀ c))
    (simplex_zero_unique (Convexity.StdSimplex.map a.toOrderHom z)))

lemma nerveOrderMap_const {P Q:Type u} [Preorder P] [Preorder Q] (c:Q) :
    nerveOrderMap (OrderHom.const P c)=ContinuousMap.const _ (nerveVertex Q c) := by
  have he:SSet.toTop.map (nerveMap (OrderHom.const P c).toFunctor)=TopCat.const (X:=|nerve P|) (nerveVertex Q c):=by
    apply (sSetTopAdj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit,Adjunction.homEquiv_unit]
    ext n x
    apply (toSimp _ n).injective
    ext z
    change SSet.toTop.map (nerveMap (OrderHom.const P c).toFunctor) (realizeSimplex (nerve P) x z)=nerveVertex Q c
    rw [realizeSimplex_map,realizeSimplex_const]
  exact congrArg TopCat.Hom.hom he

theorem nerve_contractible_of_order_clip {P:Type u} [Preorder P]
    (e:P→o P) (c:P) (he:∀p,e p≤p) (hc:∀p,e p ≤ c) : ContractibleSpace |nerve P| := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨nerveVertex P c,?_⟩
  have hh:ContinuousMap.Homotopic (nerveOrderMap (OrderHom.id (α:=P)))
      (nerveOrderMap (OrderHom.const P c)):=
    ⟨(nerveOrderComparisonHomotopy e (OrderHom.id (α:=P)) he).symm.trans
      (nerveOrderComparisonHomotopy e (OrderHom.const P c) hc)⟩
  simpa only [nerveOrderMap_id,nerveOrderMap_const] using hh

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_EarlierUpperContractible
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem sourceEarlierUpper_contractible (P:Deligne M)
    (h:Nonempty (SourceEarlierUpper M P)) :
    ContractibleSpace |nerve (SourceEarlierUpper M P)| := by
  have ha:=(sourceEarlierUpper_nonempty_iff M P).mp h
  exact nerve_contractible_of_order_clip (sourceUpperRetraction M P)
    (sourceUpperCenter M P ha) (sourceUpperRetraction_le M P)
    (sourceUpperRetraction_le_center M P ha)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightHomeomorph
attribute [-instance] _root_.OAI.HarmonicArtin.WeightContractionPiece.instReflExtends _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

lemma weightSubset_comp (A B C:Set P) (h:A⊆B) (k:B⊆C) :
    (weightSubset B C k).comp (weightSubset A B h)=weightSubset A C (h.trans k) :=rfl

variable (r:P→P→Prop) (c:P)

namespace WeightContractionPiece
variable {r c}

lemma extends_trans {a b d:WeightContractionPiece r c} (h:a.Extends b) (k:b.Extends d) : a.Extends d := by
  obtain ⟨h,hh⟩:=h
  obtain ⟨k,hk⟩:=k
  refine ⟨h.trans k,?_⟩
  intro t w
  rw [hh,hk,weightMap_comp]
  rfl

end WeightContractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LateDelay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Topology

attribute [local instance] Classical.propDecidable
universe u v
variable {A:Type u} {X:Type v} [TopologicalSpace A] [TopologicalSpace X] [T2Space X]

variable (i:C(A,X)) (r:C(X,A)) (hr:∀a,r (i a)=a)
  (D:ContinuousMap.HomotopyRel (ContinuousMap.id X) (i.comp r) (Set.range i))
  (δ:C(X,I)) (hd:∀x,δ x<1) (hz:∀x,δ x=0↔x∈Set.range i)
  (c:A) (H:ContinuousMap.Homotopy (ContinuousMap.id A) (ContinuousMap.const A c))

include hr in
lemma extendContraction_old (t:I) (a:A) :
    extendContraction i r D δ hd hz c H (t,i a)=i (H (t,a)) := by
  have he:δ (i a)=0:=(hz _).mpr ⟨a,rfl⟩
  have hlate:δ (i a)≤t:=he ▸ t.property.1
  change extensionValue i r D δ hd hz c H (t,i a)=_
  rw [show (t,i a)=(⟨(t,i a),hlate⟩:LateDelay δ).val from rfl,extensionValue_late]
  change i (H (lateDelayTime δ hd ⟨(t,i a),hlate⟩,r (i a)))=_
  have ht:lateDelayTime δ hd ⟨(t,i a),hlate⟩=t:=by
    apply Subtype.ext
    simp [lateDelayTime,he]
  rw [ht,hr]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightVertexRetract
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u
variable {P:Type u} [PartialOrder P] (v:P)
  (c:OrderWeights (WeightLink v))
  (H:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ c))

variable (a:OrderWeights (WeightOld v))
  (K:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ a))

lemma weightExtendContraction_old (t:I) (w:OrderWeights (WeightOld v)) :
    weightExtendContraction v c H a K (t,weightOldMap v w)=weightOldMap v (K (t,w)) :=
  extendContraction_old (weightOldMap v) (weightVertexRetract v c H)
    (weightVertexRetract_old v c H) (weightVertexDeformation v c H)
    (weightVertexDelay v) (weightVertexDelay_lt v) (weightVertexDelay_zero v) a K t w

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_InsertOldIso
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

variable (A:Set P) (v:P) (hv:v∉A)
  (l:OrderWeights (WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A))))
  (L:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ l))
  (a:OrderWeights A) (H:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ a))

lemma weightInsertContraction_old (t:I) (w:OrderWeights A) :
    weightInsertContraction A v hv l L a H (t,weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w)=
      weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) (H (t,w)) := by
  let e:=weightHomeomorph (insertOldIso A v hv)
  have he:weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w=
      weightOldMap (⟨v,Set.mem_insert v A⟩:↥(insert v A)) (e w):=by
    change _=weightMap (weightOldIncl _) (weightMap (OrderHomClass.toOrderHom (insertOldIso A v hv)) w)
    rw [weightMap_comp,insertOldIso_incl]
  rw [he]
  change weightExtendContraction _ l L (e a) (transportContraction e a H) (t,weightOldMap _ (e w))=_
  rw [weightExtendContraction_old]
  change weightMap (weightOldIncl _) (e (H (t,e.symm (e w))))=_
  rw [e.symm_apply_apply]
  change weightMap (weightOldIncl _) (weightMap (OrderHomClass.toOrderHom (insertOldIso A v hv)) (H (t,w)))=_
  rw [weightMap_comp,insertOldIso_incl]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnionCarrier
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] {r:P→P→Prop} {c:P}
namespace WeightContractionPiece

variable (C:Set (WeightContractionPiece r c)) (hc:IsChain Extends C) (hne:C.Nonempty)

lemma extends_union {a:WeightContractionPiece r c} (ha:a∈C) : a.Extends (union C hc hne) := by
  refine ⟨subset_union C ha,?_⟩
  intro t w
  change weightMap a.inclusion (a.hom (t,w))=
    weightMap (weightInclusion (unionCarrier C)) (unionMap C hc hne (t,weightMap (unionIncl C ⟨a,ha⟩) w))
  rw [unionMap_on,weightMap_comp]
  rfl

end WeightContractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Initial
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

variable {r:P→P→Prop} {c:P}
namespace WeightContractionPiece

variable (wf:WellFounded r) (htotal:∀x y,x≠y → r x y ∨ r y x)

include wf htotal in
lemma missing_minimal (a:WeightContractionPiece r c) (ha:∃x,x∉a.carrier) :
    ∃v,v∉a.carrier ∧ ∀x,x∈a.carrier↔r x v := by
  obtain ⟨v,hv,hm⟩:=wf.has_min a.carrierᶜ ha
  refine ⟨v,hv,?_⟩
  intro x
  constructor
  · intro hx
    have hne:x≠v:=by intro he;exact hv (he ▸ hx)
    rcases htotal x v hne with h|h
    · exact h
    · exact (hv (a.down hx h)).elim
  · intro h
    by_contra hn
    exact hm x hn h

variable (a:WeightContractionPiece r c) (v:P) (hv:v∉a.carrier)
  (heA:∀x,x∈a.carrier↔r x v)
  (hlink:ContractibleSpace (OrderWeights (WeightEarlierLink r v)))

lemma extends_successor : a.Extends (successor wf a v hv heA hlink) := by
  refine ⟨Set.subset_insert v a.carrier,?_⟩
  intro t w
  change weightMap a.inclusion (a.hom (t,w))=
    weightMap (weightInclusion (insert v a.carrier))
      (weightInsertContraction a.carrier v hv (insertLinkContractionPoint wf a v heA hlink)
        (insertLinkContraction wf a v heA hlink) (weightVertex ⟨c,a.root_mem⟩) a.hom
        (t,weightMap (weightSubset a.carrier (insert v a.carrier) (Set.subset_insert v a.carrier)) w))
  rw [weightInsertContraction_old,weightMap_comp]
  rfl

end WeightContractionPiece

theorem orderWeights_contractible_of_earlier_links (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (c:P) (hc:∀x,¬r x c)
    (hl:∀v,v≠c → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  let : Nonempty (WeightContractionPiece r c) := ⟨WeightContractionPiece.initial hc⟩
  obtain ⟨a,ha⟩:=exists_maximal_of_nonempty_chains_bounded
    (r:=@WeightContractionPiece.Extends P _ r c)
    (fun C hc hn=>⟨WeightContractionPiece.union C hc hn,
      fun a ha=>WeightContractionPiece.extends_union C hc hn ha⟩)
    WeightContractionPiece.extends_trans
  have hfull:∀x,x∈a.carrier:=by
    by_contra hn
    have he:∃x,x∉a.carrier:=not_forall.mp hn
    obtain ⟨v,hv,heA⟩:=WeightContractionPiece.missing_minimal wf htotal a he
    have hvc:v≠c:=by intro he;exact hv (he ▸ a.root_mem)
    have hnext:=WeightContractionPiece.extends_successor wf a v hv heA (hl v hvc)
    have hback:=ha _ hnext
    exact hv (hback.choose (Set.mem_insert v a.carrier))
  let e:a.carrier≃oP:={
    toFun:=Subtype.val
    invFun:=fun x=>⟨x,hfull x⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact (contractible_iff_id_nullhomotopic _).mpr
    ⟨weightHomeomorph e (weightVertex ⟨c,a.root_mem⟩),
      ⟨transportContraction (weightHomeomorph e) _ a.hom⟩⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_ContractionPoint
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

theorem orderWeights_contractible_of_piece (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (c:P) (a0:WeightContractionPiece r c)
    (hl:∀v,v∉a0.carrier → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  let X:Type u:={a:WeightContractionPiece r c // a0.Extends a}
  let R:X→X→Prop:=fun a b=>a.val.Extends b.val
  let : Nonempty X := ⟨a0,WeightContractionPiece.extends_refl a0⟩
  have hbound:∀C:Set X,IsChain R C→C.Nonempty→∃ub:X,∀a∈C,R a ub:=by
    intro C hc hn
    let D:Set (WeightContractionPiece r c):=Subtype.val '' C
    have hd:IsChain WeightContractionPiece.Extends D:=by
      rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ hne
      exact hc ha hb (fun he=>hne (congrArg Subtype.val he))
    have hdn:D.Nonempty:=hn.image Subtype.val
    let u:=WeightContractionPiece.union D hd hdn
    have h0:a0.Extends u:=by
      obtain ⟨a,ha⟩:=hn
      exact WeightContractionPiece.extends_trans a.property
        (WeightContractionPiece.extends_union D hd hdn ⟨a,ha,rfl⟩)
    refine ⟨⟨u,h0⟩,?_⟩
    intro a ha
    exact WeightContractionPiece.extends_union D hd hdn ⟨a,ha,rfl⟩
  obtain ⟨a,ha⟩:=exists_maximal_of_nonempty_chains_bounded (r:=R) hbound
    (fun hab hbd=>WeightContractionPiece.extends_trans hab hbd)
  have hfull:∀x,x∈a.val.carrier:=by
    by_contra hn
    obtain ⟨v,hv,heA⟩:=WeightContractionPiece.missing_minimal wf htotal a.val (not_forall.mp hn)
    have hv0:v∉a0.carrier:=fun he=>hv (a.property.choose he)
    let b:=WeightContractionPiece.successor wf a.val v hv heA (hl v hv0)
    have hab:a.val.Extends b:=WeightContractionPiece.extends_successor wf a.val v hv heA (hl v hv0)
    let z:X:=⟨b,WeightContractionPiece.extends_trans a.property hab⟩
    have hback:=ha z hab
    exact hv (hback.choose (Set.mem_insert v a.val.carrier))
  let e:a.val.carrier≃oP:={
    toFun:=Subtype.val
    invFun:=fun x=>⟨x,hfull x⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact (contractible_iff_id_nullhomotopic _).mpr
    ⟨weightHomeomorph e (weightVertex ⟨c,a.val.root_mem⟩),
      ⟨transportContraction (weightHomeomorph e) _ a.val.hom⟩⟩

theorem orderWeights_contractible_of_initial (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (A:Set P)
    (hdown:∀{x y},x∈A → r y x → y∈A)
    (hA:ContractibleSpace (OrderWeights A))
    (hl:∀v,v∉A → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  obtain ⟨a,⟨H⟩⟩:=@id_nullhomotopic _ _ hA
  obtain ⟨v,hv⟩:=a.support_nonempty
  let c:P:=v.val

  let H':ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights A))
      (ContinuousMap.const _ (weightVertex v)):=
    contractionToPoint a H (weightVertex v)
  let a0:WeightContractionPiece r c:={
    carrier:=A
    root_mem:=v.property
    down:=hdown
    hom:=H' }
  exact orderWeights_contractible_of_piece r wf htotal c a0 hl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightJoinKey
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

omit [PartialOrder P] in
lemma weightJoinEarlier_wf (A:Set P) (d:P→ℕ) : WellFounded (WeightJoinEarlier A d) :=
  InvImage.wf (fun x=>(weightJoinKey A d x,x))
    (wellFounded_lt.prod_lex WellOrderingRel.isWellOrder.wf)

omit [PartialOrder P] in
lemma weightJoinEarlier_total (A:Set P) (d:P→ℕ) (x y:P) (h:x≠y) :
    WeightJoinEarlier A d x y ∨ WeightJoinEarlier A d y x := by
  rw [weightJoinEarlier_iff,weightJoinEarlier_iff]
  rcases lt_trichotomy (weightJoinKey A d x) (weightJoinKey A d y) with h'|he|h'
  · exact Or.inl (Or.inl h')
  · rcases trichotomous_of WellOrderingRel x y with hl|he'|hr
    · exact Or.inl (Or.inr ⟨he,hl⟩)
    · exact (h he').elim
    · exact Or.inr (Or.inr ⟨he.symm,hr⟩)
  · exact Or.inr (Or.inl h')

omit [PartialOrder P] in
lemma weightJoinEarlier_initial (A:Set P) (d:P→ℕ) {x y:P} (hx:x∈A)
    (hy:WeightJoinEarlier A d y x) : y∈A := by
  by_contra hn
  rw [weightJoinEarlier_iff] at hy
  simp [weightJoinKey,hx,hn] at hy

theorem weightJoin_contractible (N:ℕ) : ∀{P:Type u} [PartialOrder P]
    (A:Set P) (d:P→ℕ),
    (∀x,x∉A → d x<N) →
    (∀{x y},x∉A → y∉A → x<y → d y<d x) →
    (∀{a b},a∈A → b∉A → a≤b) →
    ContractibleSpace (OrderWeights A) → ContractibleSpace (OrderWeights P) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro P inst A d hb hd hcross hA
    let r:=WeightJoinEarlier A d
    apply orderWeights_contractible_of_initial r (weightJoinEarlier_wf A d)
      (weightJoinEarlier_total A d) A (weightJoinEarlier_initial A d) hA
    intro v hv
    let L:=WeightEarlierLink r v
    let A':Set L:={x | x.val∈A}
    have hne (x:L) : x.val≠v := by
      intro he
      have hr:=x.property.1
      rw [he] at hr
      exact (weightJoinEarlier_wf A d).irrefl.irrefl v hr
    have hupper (x:L) (hx:x∉A') : v<x.val := by
      have hr:WeightJoinEarlier A d x.val v:=x.property.1
      rw [weightJoinEarlier_iff] at hr
      have hx':x.val∉A:=hx
      simp [weightJoinKey,hx',hv] at hr
      rcases x.property.2 with hl|hu
      · have lt:x.val<v:=lt_of_le_of_ne hl (hne x)
        have :=hd hx' hv lt
        omega
      · exact lt_of_le_of_ne hu (hne x).symm
    let e:A≃oA':={
      toFun:=fun a=>⟨⟨a.val,weightJoinEarlier_old A d a.property hv,
        Or.inl (hcross a.property hv)⟩,a.property⟩
      invFun:=fun a=>⟨a.val.val,a.property⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl
      map_rel_iff':=by intros;rfl }
    have hA':ContractibleSpace (OrderWeights A'):=
      (weightHomeomorph e).contractibleSpace_iff.mp hA
    exact ih (d v) (hb v hv) A' (fun x:L=>d x.val)
      (fun x hx=>hd hv hx (hupper x hx))
      (by intro x y hx hy hxy;exact hd hx hy hxy)
      (by intro a b ha hb;exact hcross ha hb) hA'

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightEarlierLower
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma weightLink_lower_cross (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    {a b:WeightEarlierLink r v} (ha:a.val<v) (hb:¬b.val<v) : a≤b := by
  rcases b.property.2 with h|h
  · rcases lt_or_eq_of_le h with hl|he
    · exact (hb hl).elim
    · have hr:=b.property.1
      rw [he] at hr
      exact (hirr v hr).elim
  · exact ha.le.trans h

theorem weightLink_contractible_of_lower (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (h:ContractibleSpace (OrderWeights (WeightEarlierLower r v))) :
    ContractibleSpace (OrderWeights (WeightEarlierLink r v)) := by
  let A:Set (WeightEarlierLink r v):={x | x.val<v}
  have hA:ContractibleSpace (OrderWeights A):=(weightHomeomorph (earlierLowerIso r v)).contractibleSpace_iff.mp h
  apply weightJoin_contractible (N+1) A (fun x=>N-k x.val)
    (fun x _=>by omega) ?_ (weightLink_lower_cross r hirr v) hA
  intro x y hx hy hxy
  have hlt:k x.val<k y.val:=hmono hxy
  have hb:=hk y.val
  omega

theorem weightJoin_contractible_upper (N:ℕ) (A:Set P) (k:P→ℕ)
    (hk:∀x,x∈A → k x<N)
    (hmono:∀{x y},x∈A → y∈A → x<y → k x<k y)
    (hcross:∀{a b},a∈A → b∉A → a≤b)
    (hB:ContractibleSpace (OrderWeights (Aᶜ:Set P))) : ContractibleSpace (OrderWeights P) := by
  have hdual:ContractibleSpace (OrderWeights Pᵒᵈ):=by
    apply weightJoin_contractible N (Aᶜ:Set Pᵒᵈ) k
    · intro x hx
      exact hk x (not_not.mp hx)
    · intro x y hx hy hxy
      exact hmono (not_not.mp hy) (not_not.mp hx) hxy
    · intro a b ha hb
      exact hcross (not_not.mp hb) ha
    · exact (weightDualHomeomorph (P:=(Aᶜ:Set P))).contractibleSpace_iff.mp hB
  exact (weightDualHomeomorph (P:=P)).contractibleSpace_iff.mpr hdual

theorem weightLink_contractible_of_upper (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (h:ContractibleSpace (OrderWeights (WeightEarlierUpper r v))) :
    ContractibleSpace (OrderWeights (WeightEarlierLink r v)) := by
  let A:Set (WeightEarlierLink r v):={x | x.val<v}
  have hB:ContractibleSpace (OrderWeights (Aᶜ:Set (WeightEarlierLink r v))):=
    (weightHomeomorph (earlierUpperIso r hirr v)).contractibleSpace_iff.mp h
  apply weightJoin_contractible_upper (N+1) A (fun x=>k x.val)
    (fun x _=>Nat.lt_succ_of_le (hk x.val))
    (by intro x y _ _ hxy;exact hmono hxy) (weightLink_lower_cross r hirr v) hB

lemma weightLink_nonempty_parts (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (h:Nonempty (WeightEarlierLink r v)) :
    Nonempty (WeightEarlierLower r v) ∨ Nonempty (WeightEarlierUpper r v) := by
  obtain ⟨x,hx,hcmp⟩:=h
  have hne:x≠v:=by intro he;exact hirr v (he ▸ hx)
  exact hcmp.elim (fun h=>Or.inl ⟨x,hx,lt_of_le_of_ne h hne⟩)
    (fun h=>Or.inr ⟨x,hx,lt_of_le_of_ne h hne.symm⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_OrderWeightsContractibleLower
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

theorem orderWeights_contractible_of_lower_fibers (A:Set P) (k:P→ℕ) (N:ℕ)
    (hk:∀x,k x≤N) (hm:StrictMono k) (hA:ContractibleSpace (OrderWeights A))
    (hf:∀v,v∉A → ContractibleSpace (OrderWeights {x:P // x∈A ∧ x<v})) :
    ContractibleSpace (OrderWeights P) := by
  let d:P→ℕ:=fun x=>N-k x
  let r:=WeightJoinEarlier A d
  have hw:=weightJoinEarlier_wf A d
  apply orderWeights_contractible_of_initial r hw (weightJoinEarlier_total A d) A
    (weightJoinEarlier_initial A d) hA
  intro v hv
  have he:∀x,x<v → (r x v ↔ x∈A):=by
    intro x hx
    constructor
    · intro hr
      by_contra hn
      change WeightJoinEarlier A d x v at hr
      rw [weightJoinEarlier_iff] at hr
      have hlt:=hm hx
      have hb:=hk v
      simp [weightJoinKey,hn,hv,d] at hr
      omega
    · intro ha
      exact weightJoinEarlier_old A d ha hv
  let e:WeightEarlierLower r v ≃o {x:P // x∈A ∧ x<v}:={
    toFun:=fun x=>⟨x.val,(he x.val x.property.2).mp x.property.1,x.property.2⟩
    invFun:=fun x=>⟨x.val,(he x.val x.property.2).mpr x.property.1,x.property.2⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact weightLink_contractible_of_lower r (fun x=>hw.irrefl.irrefl x) v k N hk hm
    ((weightHomeomorph e).contractibleSpace_iff.mpr (hf v hv))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_OrderWeightsContractibleUnique
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

theorem orderWeights_contractible_unique_source (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (hl:∀v,Nonempty (WeightEarlierLower r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLower r v)))
    (hu:∀v,Nonempty (WeightEarlierUpper r v) →
      ContractibleSpace (OrderWeights (WeightEarlierUpper r v)))
    (hs:∀x y,¬Nonempty (WeightEarlierLink r x) →
      ¬Nonempty (WeightEarlierLink r y) → x=y)
    (hne:Nonempty P) : ContractibleSpace (OrderWeights P) := by
  obtain ⟨c,_,hc⟩:=wf.has_min Set.univ (by obtain ⟨x⟩:=hne;exact ⟨x,Set.mem_univ _⟩)
  have hc':∀x,¬r x c:=fun x=>hc x (Set.mem_univ x)
  have hcL:¬Nonempty (WeightEarlierLink r c):=by
    rintro ⟨x,hx,_⟩
    exact hc' x hx
  apply orderWeights_contractible_of_earlier_links r wf htotal c hc'
  intro v hv
  have hn:Nonempty (WeightEarlierLink r v):=by
    by_contra hn
    exact hv (hs v c hn hcL)
  rcases weightLink_nonempty_parts r (fun x=>wf.irrefl.irrefl x) v hn with h|h
  · exact weightLink_contractible_of_lower r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hl v h)
  · exact weightLink_contractible_of_upper r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hu v h)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_DeligneRankBound
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [LinearOrder S] in
lemma sourceDeligne_rank_bound (X:Deligne M) : X.val.1.ncard≤Fintype.card S := by
  simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card X.val.1
omit [LinearOrder S] in
lemma sourceDeligne_rank_strictMono : StrictMono (fun X:Deligne M=>X.val.1.ncard) := by
  intro X Y h
  exact Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightColor
attribute [-instance] _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} [PartialOrder P]

lemma weightColor_eq {A:Type v} (f:P→A) (hf:∀x y,x≤y → f x=f y)
    (w:OrderWeights P) (p:P) (hp:p∈w.weights.support) : weightColor f w=f p := by
  rcases w.chain (Classical.choose w.support_nonempty) (Classical.choose_spec w.support_nonempty) p hp with h|h
  · exact hf _ _ h
  · exact (hf _ _ h).symm

lemma weightColor_continuous {A:Type v} [TopologicalSpace A] (f:P→A)
    (hf:∀x y,x≤y → f x=f y) : Continuous (weightColor f) := by
  rw [orderWeights_continuous_iff]
  intro n x
  have he: (fun z=>weightColor f (orderWeightsOfChain (nerveChain x) z))=
      (fun _ : Convexity.StdSimplex ℝ (Fin (n.len+1))=>f (nerveChain x 0)) := by
    funext z
    let w:=orderWeightsOfChain (nerveChain x) z
    have hp:Classical.choose w.support_nonempty∈(chainWeights (nerveChain x) z).support:=Classical.choose_spec w.support_nonempty
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp (chainWeights_support (nerveChain x) z hp)
    change f (Classical.choose w.support_nonempty)=_
    rw [←hj]
    exact (hf _ _ ((nerveChain x).monotone (Fin.zero_le j))).symm
  rw [he]
  exact continuous_const

lemma weightColor_vertex {A:Type v} (f:P→A) (hf:∀x y,x≤y → f x=f y) (p:P) :
    weightColor f (weightVertex p)=f p := by
  apply weightColor_eq f hf
  simp [weightVertex]

lemma orderWeights_colors_eq {A:Type v} (h:ContractibleSpace (OrderWeights P))
    (f:P→A) (hf:∀x y,x≤y → f x=f y) (x y:P) : f x=f y := by
  let _ := h
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have he:=PreconnectedSpace.constant (inferInstance:PreconnectedSpace (OrderWeights P))
    (weightColor_continuous f hf) (x:=weightVertex x) (y:=weightVertex y)
  simpa only [weightColor_vertex f hf] using he

variable (r:P→P→Prop) (wf:WellFounded r)

lemma weightSource_eq (v:P) : weightSource r wf v=
    if h:Nonempty (WeightEarlierLink r v) then
      weightSource r wf (Classical.choice h).val else v := by
  rw [weightSource,WellFounded.fix_eq]

lemma weightSource_of_empty (v:P) (h:¬Nonempty (WeightEarlierLink r v)) :
    weightSource r wf v=v := by rw [weightSource_eq,dite_eq_right h]

lemma weightSource_near (htotal:∀x y,x≠y → r x y ∨ r y x)
    (hl:∀v,Nonempty (WeightEarlierLink r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ∀v x,r x v → (x≤v ∨ v≤x) → weightSource r wf x=weightSource r wf v := by
  intro v
  induction v using wf.induction with
  | h v ih =>
    intro x hx hcomp
    have hn:Nonempty (WeightEarlierLink r v):=⟨⟨x,hx,hcomp⟩⟩
    have hcolor:∀a b:WeightEarlierLink r v,a≤b →
        weightSource r wf a.val=weightSource r wf b.val:=by
      intro a b hab
      by_cases he:a.val=b.val
      · rw [he]
      · rcases htotal a b he with h|h
        · exact ih b b.property.1 a h (Or.inl hab)
        · exact (ih a a.property.1 b h (Or.inr hab)).symm
    rw [weightSource_eq r wf v,dite_eq_left hn]
    exact orderWeights_colors_eq (hl v hn) (fun a=>weightSource r wf a.val) hcolor
      ⟨x,hx,hcomp⟩ (Classical.choice hn)

lemma weightSource_comparable (htotal:∀x y,x≠y → r x y ∨ r y x)
    (hl:∀v,Nonempty (WeightEarlierLink r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLink r v)))
    (x y:P) (h:x≤y) : weightSource r wf x=weightSource r wf y := by
  by_cases he:x=y
  · rw [he]
  · rcases htotal x y he with he|he
    · exact weightSource_near r wf htotal hl y x he (Or.inl h)
    · exact (weightSource_near r wf htotal hl x y he (Or.inr h)).symm

include wf in

theorem orderWeights_contractible_connected [CategoryTheory.IsConnected P]
    (htotal:∀x y,x≠y → r x y ∨ r y x)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (hl:∀v,Nonempty (WeightEarlierLower r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLower r v)))
    (hu:∀v,Nonempty (WeightEarlierUpper r v) →
      ContractibleSpace (OrderWeights (WeightEarlierUpper r v))) :
    ContractibleSpace (OrderWeights P) := by
  have hlink:∀v,Nonempty (WeightEarlierLink r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLink r v)):=by
    intro v hv
    rcases weightLink_nonempty_parts r (fun x=>wf.irrefl.irrefl x) v hv with h|h
    · exact weightLink_contractible_of_lower r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hl v h)
    · exact weightLink_contractible_of_upper r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hu v h)
  apply orderWeights_contractible_unique_source r wf htotal k N hk hmono hl hu ?_ inferInstance
  intro x y hx hy
  have he:=CategoryTheory.constant_of_preserves_morphisms (weightSource r wf)
    (fun a b hab=>weightSource_comparable r wf htotal hlink a b (leOfHom hab)) x y
  simpa only [weightSource_of_empty r wf x hx,weightSource_of_empty r wf y hy] using he

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlierLowerOrderIso
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CategoryTheory Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem sourceDeligne_contractible : ContractibleSpace (DeligneRealization M) := by
  let:=deligne_connected M
  apply nerveWeightsHomeomorph.contractibleSpace_iff.mpr
  apply orderWeights_contractible_connected (SourceEarlier M) (sourceEarlier_wellFounded M)
    (fun x y h=>by
      rcases sourceEarlier_trichotomy M x y with h'|h'|h'
      · exact Or.inl h'
      · exact (h h').elim
      · exact Or.inr h')
    (fun P=>P.val.1.ncard) (Fintype.card S) (sourceDeligne_rank_bound M)
    (sourceDeligne_rank_strictMono M)
  · intro P h
    let e:=sourceEarlierLowerOrderIso M P
    exact (weightHomeomorph e).contractibleSpace_iff.mpr
      (nerveWeightsHomeomorph.contractibleSpace_iff.mp
        (sourceEarlierLower_contractible M P (Nonempty.map e h)))
  · intro P h
    let e:=sourceEarlierUpperOrderIso M P
    exact (weightHomeomorph e).contractibleSpace_iff.mpr
      (nerveWeightsHomeomorph.contractibleSpace_iff.mp
        (sourceEarlierUpper_contractible M P (Nonempty.map e h)))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ArtinReindex
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {S:Type u} {T:Type v} (M:CoxeterMatrix S) (e:S≃T)

theorem deligne_contractible [Finite S] : ContractibleSpace (DeligneRealization M) := by
  let :=Fintype.ofFinite S
  let e:=Fintype.equivFin S
  have hc:ContractibleSpace (OrderWeights (Deligne (M.reindex e))):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (sourceDeligne_contractible (M.reindex e))
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    ((weightHomeomorph (deligneReindex M e)).contractibleSpace_iff.mpr hc)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_OrderMappingCylinder
attribute [-instance] _root_.OAI.HarmonicArtin.finiteLinearWeightsCompact _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.instT2SpaceOrderWeights _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial

universe u
variable {P Q:Type u} [PartialOrder P] [PartialOrder Q]

namespace OrderMappingCylinder
variable (f:P→oQ)

lemma weights_contractible (h:ContractibleSpace (OrderWeights Q)) :
    ContractibleSpace (OrderWeights (OrderMappingCylinder f)) := by
  have hQ:=nerveWeightsHomeomorph.contractibleSpace_iff.mpr h
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mp ((nerveEquiv f).contractibleSpace_iff.mpr hQ)

lemma not_old_iff (x:OrderMappingCylinder f) : x∉old f ↔ ∃q,x=Sum.inr q := by
  cases x with
  | inl p=>
    constructor
    · intro hn;exact (hn ⟨p,rfl⟩).elim
    · rintro ⟨q,h⟩;cases h
  | inr q=>
    refine ⟨fun _=>⟨q,rfl⟩,?_⟩
    rintro _ ⟨p,h⟩
    cases h

lemma rank_bound (k:P→ℕ) (l:Q→ℕ) (N L:ℕ) (hk:∀p,k p≤N) (hl:∀q,l q≤L)
    (x:OrderMappingCylinder f) : rank f k l N x≤N+1+L := by
  cases x with
  | inl p=>have:=hk p;dsimp [rank];omega
  | inr q=>have:=hl q;dsimp [rank];omega

lemma rank_strict (k:P→ℕ) (l:Q→ℕ) (N:ℕ) (hk:∀p,k p≤N)
    (hkm:StrictMono k) (hlm:StrictMono l) : StrictMono (rank f k l N) := by
  intro x y h
  rw [lt_iff_le_not_ge] at h
  cases x with
  | inl p=>cases y with
    | inl p'=>exact hkm (lt_iff_le_not_ge.mpr h)
    | inr q=>have:=hk p;dsimp [rank];omega
  | inr q=>cases y with
    | inl p=>exact h.1.elim
    | inr q'=>exact Nat.add_lt_add_left (hlm (lt_iff_le_not_ge.mpr h)) _

end OrderMappingCylinder
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightRetractionPiece
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] (r:P→P→Prop) (A:Set P)

namespace WeightRetractionPiece
variable {r A}

lemma extends_trans {a b c:WeightRetractionPiece r A} (h:a.Extends b) (k:b.Extends c) : a.Extends c := by
  obtain ⟨h,hh⟩:=h
  obtain ⟨k,hk⟩:=k
  refine ⟨h.trans k,?_⟩
  intro w
  rw [← weightSubset_comp _ _ _ h k,← weightMap_comp,hk,hh]

variable (C:Set (WeightRetractionPiece r A)) (hc:IsChain Extends C) (hne:C.Nonempty)

lemma extends_union {a:WeightRetractionPiece r A} (ha:a∈C) : a.Extends (union C hc hne) :=
  ⟨subset_union C ha,fun w=>unionMap_on C hc hne ⟨a,ha⟩ w⟩

end WeightRetractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightInsertRetract
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

namespace WeightRetractionPiece
variable {r:P→P→Prop} {A:Set P}

variable (wf:WellFounded r) (htotal:∀x y,x≠y → r x y ∨ r y x)

include wf htotal in
lemma missing_minimal (a:WeightRetractionPiece r A) (ha:∃x,x∉a.carrier) :
    ∃v,v∉a.carrier ∧ ∀x,x∈a.carrier↔r x v := by
  obtain ⟨v,hv,hm⟩:=wf.has_min a.carrierᶜ ha
  refine ⟨v,hv,?_⟩
  intro x
  constructor
  · intro hx
    have hne:x≠v:=by intro he;exact hv (he ▸ hx)
    rcases htotal x v hne with h|h
    · exact h
    · exact (hv (a.down hx h)).elim
  · intro h
    by_contra hn
    exact hm x hn h

variable (a:WeightRetractionPiece r A) (v:P) (hv:v∉a.carrier)
  (heA:∀x,x∈a.carrier↔r x v)
  (hlink:ContractibleSpace (OrderWeights (WeightEarlierLink r v)))

lemma extends_successor : a.Extends (successor wf a v hv heA hlink) := by
  refine ⟨Set.subset_insert v a.carrier,?_⟩
  intro w
  change a.map (weightInsertRetract _ _ _ _ (weightMap _ w))=a.map w
  exact congrArg a.map (weightInsertRetract_old a.carrier v hv
    (insertLinkContractible wf a v heA hlink) w)

end WeightRetractionPiece

theorem orderWeights_retract_of_initial (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (A:Set P)
    (hdown:∀{x y},x∈A → r y x → y∈A)
    (hl:∀v,v∉A → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ∃f:C(OrderWeights P,OrderWeights A),∀w:OrderWeights A,f (weightMap (weightInclusion A) w)=w := by
  let :Nonempty (WeightRetractionPiece r A):=⟨WeightRetractionPiece.initial hdown⟩
  obtain ⟨a,ha⟩:=exists_maximal_of_nonempty_chains_bounded
    (r:=@WeightRetractionPiece.Extends P _ r A)
    (fun C hc hn=>⟨WeightRetractionPiece.union C hc hn,
      fun a ha=>WeightRetractionPiece.extends_union C hc hn ha⟩)
    WeightRetractionPiece.extends_trans
  have hfull:∀x,x∈a.carrier:=by
    by_contra hn
    obtain ⟨v,hv,heA⟩:=WeightRetractionPiece.missing_minimal wf htotal a (not_forall.mp hn)
    have hvA:v∉A:=fun h=>hv (a.base h)
    have hnext:=WeightRetractionPiece.extends_successor wf a v hv heA (hl v hvA)
    have hback:=ha _ hnext
    exact hv (hback.choose (Set.mem_insert v a.carrier))
  let e:a.carrier≃oP:={
    toFun:=Subtype.val
    invFun:=fun x=>⟨x,hfull x⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  refine ⟨a.map.comp ⟨(weightHomeomorph e).symm,(weightHomeomorph e).symm.continuous⟩,?_⟩
  intro w
  change a.map (weightMap (e.symm:P→o a.carrier) (weightMap (weightInclusion A) w))=w
  rw [weightMap_comp]
  exact a.retract w

theorem orderWeights_retract_of_lower_fibers (A:Set P) (k:P→ℕ) (N:ℕ)
    (hk:∀x,k x≤N) (hm:StrictMono k)
    (hf:∀v,v∉A → ContractibleSpace (OrderWeights {x:P // x∈A ∧ x<v})) :
    ∃f:C(OrderWeights P,OrderWeights A),∀w:OrderWeights A,f (weightMap (weightInclusion A) w)=w := by
  let d:P→ℕ:=fun x=>N-k x
  let r:=WeightJoinEarlier A d
  have hw:=weightJoinEarlier_wf A d
  apply orderWeights_retract_of_initial r hw (weightJoinEarlier_total A d) A
    (weightJoinEarlier_initial A d)
  intro v hv
  have he:∀x,x<v → (r x v ↔ x∈A):=by
    intro x hx
    constructor
    · intro hr
      by_contra hn
      change WeightJoinEarlier A d x v at hr
      rw [weightJoinEarlier_iff] at hr
      have hlt:=hm hx
      have hb:=hk v
      simp [weightJoinKey,hn,hv,d] at hr
      omega
    · intro ha
      exact weightJoinEarlier_old A d ha hv
  let e:WeightEarlierLower r v ≃o {x:P // x∈A ∧ x<v}:={
    toFun:=fun x=>⟨x.val,(he x.val x.property.2).mp x.property.1,x.property.2⟩
    invFun:=fun x=>⟨x.val,(he x.val x.property.2).mpr x.property.1,x.property.2⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact weightLink_contractible_of_lower r (fun x=>hw.irrefl.irrefl x) v k N hk hm
    ((weightHomeomorph e).contractibleSpace_iff.mpr (hf v hv))

lemma contractible_of_continuous_retract {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (i:C(X,Y)) (r:C(Y,X)) (hr:∀x,r (i x)=x) (h:ContractibleSpace Y) : ContractibleSpace X := by
  obtain ⟨y,⟨H⟩⟩:=@id_nullhomotopic _ _ h
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨r y,⟨?_⟩⟩
  exact {
    toFun:=fun p=>r (H (p.1,i p.2))
    continuous_toFun:=r.continuous.comp (H.continuous.comp (continuous_fst.prodMk (i.continuous.comp continuous_snd)))
    map_zero_left:=fun x=>by rw [H.apply_zero];exact hr x
    map_one_left:=fun x=>by rw [H.apply_one];rfl }

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Earlier
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P : Type} [PartialOrder P] (f : P →o ℕ)

theorem naturalCylinder_lower_contractible (k : P → ℕ) (N : ℕ)
    (hk : ∀ p, k p ≤ N) (hkm : StrictMono k)
    (hf : ∀ n, ContractibleSpace (OrderWeights {p : P // f p ≤ n})) (n : ℕ) :
    ContractibleSpace (OrderWeights {x : OrderMappingCylinder f // x < OrderMappingCylinder.right f n}) := by
  let Q := {x : OrderMappingCylinder f // x < OrderMappingCylinder.right f n}
  let A : Set Q := {x | x.val ∈ OrderMappingCylinder.old f}
  let rank : Q → ℕ := fun x => OrderMappingCylinder.rank f k id N x.val
  have hrank : ∀ x, rank x ≤ N+n := by
    intro x
    cases hx : x.val with
    | inl p =>
      have hb := hk p
      change OrderMappingCylinder.rank f k id N x.val ≤ N+n
      rw [hx]
      change k p ≤ N+n
      omega
    | inr m =>
      have hh := x.property
      rw [hx] at hh
      change OrderMappingCylinder.right f m < OrderMappingCylinder.right f n at hh
      rw [lt_iff_le_not_ge] at hh
      change m ≤ n ∧ ¬ n ≤ m at hh
      change OrderMappingCylinder.rank f k id N x.val ≤ N+n
      rw [hx]
      change N+1+m ≤ N+n
      omega
  have hrankm : StrictMono rank := by
    intro x y h
    exact OrderMappingCylinder.rank_strict f k id N hk hkm (fun _ _ h => h) h
  have hA : ContractibleSpace (OrderWeights A) :=
    (weightHomeomorph (lowerOldIso (OrderMappingCylinder.old f) (OrderMappingCylinder.right f n))).contractibleSpace_iff.mpr
      ((weightHomeomorph (OrderMappingCylinder.oldLowerIso f n)).contractibleSpace_iff.mp (hf n))
  apply orderWeights_contractible_of_lower_fibers A rank (N+n) hrank hrankm hA
  intro v hv
  have hnv : v.val ∉ OrderMappingCylinder.old f := hv
  obtain ⟨m,hm⟩ := (OrderMappingCylinder.not_old_iff f v.val).mp hnv
  let e := lowerOldLowerIso (OrderMappingCylinder.old f) (OrderMappingCylinder.right f n) v
  rw [hm] at e
  exact (weightHomeomorph e).contractibleSpace_iff.mpr
    ((weightHomeomorph (OrderMappingCylinder.oldLowerIso f m)).contractibleSpace_iff.mp (hf m))

theorem orderWeights_contractible_of_natural_preimages (k : P → ℕ) (N : ℕ)
    (hk : ∀ p, k p ≤ N) (hkm : StrictMono k)
    (hf : ∀ n, ContractibleSpace (OrderWeights {p : P // f p ≤ n})) :
    ContractibleSpace (OrderWeights P) := by
  let r := NaturalCylinder.earlier f
  obtain ⟨g,hg⟩ := orderWeights_retract_of_initial r
    (weightJoinEarlier_wf _ _) (weightJoinEarlier_total _ _)
    (OrderMappingCylinder.old f) (weightJoinEarlier_initial _ _) (by
      intro v hv
      obtain ⟨n,rfl⟩ := (OrderMappingCylinder.not_old_iff f v).mp hv
      exact (weightHomeomorph (NaturalCylinder.linkIso f n)).contractibleSpace_iff.mpr
        (naturalCylinder_lower_contractible f k N hk hkm hf n))
  have hNat : ContractibleSpace (OrderWeights ℕ) :=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (nerve_orderBot_contractible ℕ)
  have hR := OrderMappingCylinder.weights_contractible f hNat
  have hA := contractible_of_continuous_retract
    (weightMapContinuous (weightInclusion (OrderMappingCylinder.old f))) g hg hR
  exact (weightHomeomorph (OrderMappingCylinder.oldIso f)).contractibleSpace_iff.mpr hA

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LiftedDeck
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S:Type u} (M:CoxeterMatrix S)

lemma lifted_rank_bound [Finite S] (a:LiftedCell M) : a.2.val.ncard≤Nat.card S :=
  Set.ncard_le_card _

lemma lifted_rank_strict [Finite S] : StrictMono (fun a:LiftedCell M=>a.2.val.ncard) := by
  intro a b h
  exact Set.ncard_lt_ncard (lifted_lt_type M h) (Set.toFinite _)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveDegree_mul _root_.OAI.HarmonicArtin.positiveDegree_one _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_involutive _root_.OAI.HarmonicArtin.positiveReverse_one _root_.OAI.HarmonicArtin.positiveSimpleLift_one _root_.OAI.HarmonicArtin.positiveSimpleLift_simple _root_.OAI.HarmonicArtin.positiveToCoxeter_generator _root_.OAI.HarmonicArtin.positiveToCoxeter_simpleLift _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

lemma positiveRegion_subset_of_factor (g k:Artin M) (p:PositiveArtin M)
    (h:g=k*positiveToArtin M p) : PositiveRegion M g⊆PositiveRegion M k := by
  rintro a ⟨q,hq⟩
  exact ⟨p*q,by rw [hq,h,map_mul,mul_assoc]⟩

section Spherical
variable {A:Type} [Fintype A] [LinearOrder A] (N:CoxeterMatrix A)
  (T:Set A) (hT:IsSpherical N T)

include hT in
omit [LinearOrder A] in
theorem spherical_positiveRegions_directed
    (g h:Artin (restrictedMatrix N T)) :
    ∃k:Artin (restrictedMatrix N T),
      PositiveRegion (restrictedMatrix N T) g⊆PositiveRegion (restrictedMatrix N T) k ∧
      PositiveRegion (restrictedMatrix N T) h⊆PositiveRegion (restrictedMatrix N T) k := by
  let f:=positiveToArtin (restrictedMatrix N T)
  obtain ⟨c,d,hcd⟩:=(spherical_positive_monoid_fractions N T hT (g⁻¹*h)).2
  let k:=g*(f c)⁻¹
  have hg:g=k*f c:=by dsimp [k];group
  have hh:h=k*f d:=by
    calc h=g*(g⁻¹*h):=by group
         _=g*((f c)⁻¹*f d):=by rw [hcd]
         _=k*f d:=by dsimp [k];group
  exact ⟨k,positiveRegion_subset_of_factor _ g k c hg,
    positiveRegion_subset_of_factor _ h k d hh⟩

end Spherical
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalLongest
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma cellWithTop_topVertex (a:LiftedCell M) :
    cellWithTop M (liftedTopVertex M a) a.2=a := by
  obtain ⟨g,T⟩:=a
  simp only [cellWithTop,liftedTopVertex,mul_inv_cancel_right]

lemma cellWithTop_mono (b:Artin M) {R T:SphericalType M} (hle:R.val⊆T.val) :
    cellWithTop M b R ≤ cellWithTop M b T :=
  lifted_same_top_le M R.val T.val R.property T.property hle _ _
    (sphericalLongest_spec M R) (sphericalLongest_spec M T) b

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NoncriticalPositiveCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
variable (inj:Function.Injective (positiveToArtin M))

theorem positiveMatch_ne (a:NoncriticalPositiveCell M) : positiveMatch M z hz inj a≠a := by
  intro he
  have ht:=positiveMatch_type M z hz inj a
  rw [he] at ht
  have hm:matchingLetter M z hz a∈a.val.2.val ↔ matchingLetter M z hz a∈matchingOtherType M z hz a:=by rw [ht]
  simp only [matchingOtherType] at hm
  split_ifs at hm with hs
  · simp [hs] at hm
  · simp [hs] at hm

theorem positiveMatch_incident (a:NoncriticalPositiveCell M) :
    positiveCellToLifted M a.val < positiveCellToLifted M (positiveMatch M z hz inj a).val ∨
    positiveCellToLifted M (positiveMatch M z hz inj a).val < positiveCellToLifted M a.val := by
  have hne:positiveCellToLifted M a.val ≠ positiveCellToLifted M (positiveMatch M z hz inj a).val := by
    intro he
    apply positiveMatch_ne M z hz inj a
    apply Subtype.ext
    apply Prod.ext
    · apply inj
      exact (congrArg Prod.fst he).symm
    · exact (congrArg Prod.snd he).symm
  have hcell:∀c:PositiveLiftedCell M,positiveCellToLifted M c=
      cellWithTop M (positiveToArtin M (positiveCellTop M c)) c.2:=by
    intro c
    rw [positiveCellTop_toArtin]
    exact (cellWithTop_topVertex M (positiveCellToLifted M c)).symm
  have hAB:a.val.2.val⊆(positiveMatch M z hz inj a).val.2.val ∨
      (positiveMatch M z hz inj a).val.2.val⊆a.val.2.val:=by
    rw [positiveMatch_type]
    unfold matchingOtherType
    split_ifs
    · exact Or.inr Set.sdiff_subset
    · exact Or.inl (Set.subset_insert _ _)
  rcases hAB with hab|hba
  · left
    apply lt_of_le_of_ne ?_ hne
    rw [hcell _,hcell _,positiveMatch_top]
    exact cellWithTop_mono M _ hab
  · right
    apply lt_of_le_of_ne ?_ hne.symm
    rw [hcell _,hcell _,positiveMatch_top]
    exact cellWithTop_mono M _ hba

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveCellPoset
attribute [-instance] _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] (M : CoxeterMatrix S)

variable [LinearOrder S]
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveEarlier_total (a b : PositiveCellPoset M inj) (hne : a ≠ b) :
    PositiveEarlier M z hz inj a b ∨ PositiveEarlier M z hz inj b a := by
  rw [positiveEarlier_iff,positiveEarlier_iff]
  rcases lt_trichotomy (positiveDegree M (positiveCellTop M a))
      (positiveDegree M (positiveCellTop M b)) with h|he|h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (positiveMatchingTypeKey M z hz a)
        (positiveMatchingTypeKey M z hz b) with h|he'|h
    · exact Or.inl (Or.inr ⟨he,Or.inl h⟩)
    · rcases trichotomous_of WellOrderingRel a b with h|hab|h
      · exact Or.inl (Or.inr ⟨he,Or.inr ⟨he',h⟩⟩)
      · exact (hne hab).elim
      · exact Or.inr (Or.inr ⟨he.symm,Or.inr ⟨he'.symm,h⟩⟩)
    · exact Or.inr (Or.inr ⟨he.symm,Or.inl h⟩)
  · exact Or.inr (Or.inl h)

lemma positiveEarlier_root (a : PositiveCellPoset M inj) :
    ¬PositiveEarlier M z hz inj a (positiveRootCell M) := by
  intro h
  have hr := (positiveCellTop_eq_one_iff M (positiveRootCell M)).mpr rfl
  have hd : positiveDegree M (positiveCellTop M (positiveRootCell M)) = 0 := by
    rw [hr,positiveDegree_one]
  have ha : a = positiveRootCell M := by
    apply (positiveCellTop_eq_one_iff M a).mp
    apply (positiveDegree_zero_iff M _).mp
    rw [positiveEarlier_iff,hd] at h
    omega
  subst a
  exact (positiveEarlier_wf M z hz inj).irrefl.irrefl _ h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveCellPoset2
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveMatch_below_or_above (a : NoncriticalPositiveCell M) :
    ((matchingLetter M z hz a ∉ a.val.2.val) ∧
        positiveCellToLifted M a.val < positiveCellToLifted M (positiveMatch M z hz inj a).val) ∨
      ((matchingLetter M z hz a ∈ a.val.2.val) ∧
        positiveCellToLifted M (positiveMatch M z hz inj a).val < positiveCellToLifted M a.val) := by
  have hinc := positiveMatch_incident M z hz inj a
  by_cases hs : matchingLetter M z hz a ∈ a.val.2.val
  · right; refine ⟨hs,?_⟩
    rcases hinc with h|h
    · have hsub := ((lifted_le_iff_face M _ _).mp h.le).1
      have hm := hsub hs
      change matchingLetter M z hz a ∈ (positiveMatch M z hz inj a).val.2.val at hm
      rw [positiveMatch_type,matchingOtherType,ite_eq_left hs] at hm
      exact (hm.2 (Set.mem_singleton _)).elim
    · exact h
  · left; refine ⟨hs,?_⟩
    rcases hinc with h|h
    · exact h
    · have hsub := ((lifted_le_iff_face M _ _).mp h.le).1
      exact (hs (hsub (by
        change matchingLetter M z hz a ∈ (positiveMatch M z hz inj a).val.2.val
        rw [positiveMatch_type,matchingOtherType,ite_eq_right hs]
        exact Set.mem_insert _ _))).elim

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveEarlierLinkUpper
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveMatch_upper_lt (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∉ a.val.2.val) :
    positiveCellToLifted M a.val < positiveCellToLifted M (positiveMatch M z hz inj a).val := by
  rcases positiveMatch_below_or_above M z hz inj a with h|h
  · exact h.2
  · exact (hs h.1).elim

theorem positiveEarlierLink_lower_contractible (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∉ a.val.2.val) :
    ContractibleSpace (OrderWeights (WeightEarlierLink (PositiveEarlier M z hz inj) a.val)) := by
  let b : PositiveCellPoset M inj := (positiveMatch M z hz inj a).val
  have hab : positiveCellToLifted M a.val < positiveCellToLifted M b := positiveMatch_upper_lt M z hz inj a hs
  have hba : PositiveEarlier M z hz inj b a.val := positiveMatch_before M z hz inj a hs
  let v : WeightEarlierLink (PositiveEarlier M z hz inj) a.val := ⟨b,hba,Or.inr hab.le⟩
  have hv : ∀ x : WeightEarlierLink (PositiveEarlier M z hz inj) a.val, x ≤ v := by
    intro x
    rcases x.property.2 with h|h
    · exact h.trans hab.le
    · have hne : a.val ≠ x.val := by
        intro he
        have hh := x.property.1
        rw [←he] at hh
        exact (positiveEarlier_wf M z hz inj).irrefl.irrefl _ hh
      obtain ⟨_,_,he⟩ := positiveEarlier_upper_eq M z hz inj a.val x.val
        (lt_of_le_of_ne h hne) x.property.1
      change (x.val : PositiveCellPoset M inj) ≤ b
      exact le_of_eq he.symm
  let : OrderTop (WeightEarlierLink (PositiveEarlier M z hz inj) a.val) :=
    { top := v, le_top := hv }
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mp
    (nerve_orderTop_contractible (WeightEarlierLink (PositiveEarlier M z hz inj) a.val))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlierLinkSubtypeIso
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

theorem invariantPositive_contractible (D : Set (PositiveCellPoset M inj))
    (hroot : positiveRootCell M ∈ D)
    (hdown : ∀ {a b : PositiveCellPoset M inj}, a ≤ b → b ∈ D → a ∈ D)
    (hmatch : ∀ a : NoncriticalPositiveCell M, a.val ∈ D →
      (positiveMatch M z hz inj a).val ∈ D)
    (hupper : ∀ a : NoncriticalPositiveCell M, a.val ∈ D → matchingLetter M z hz a ∈ a.val.2.val →
      ContractibleSpace (OrderWeights {x : PositiveCellPoset M inj //
        positiveCellToLifted M x < positiveCellToLifted M a.val ∧
        x ≠ (positiveMatch M z hz inj a).val})) :
    ContractibleSpace (OrderWeights D) := by
  let r : D → D → Prop := fun a b => PositiveEarlier M z hz inj a.val b.val
  have wf : WellFounded r := InvImage.wf Subtype.val (positiveEarlier_wf M z hz inj)
  apply orderWeights_contractible_of_earlier_links r wf
    (fun a b hne => positiveEarlier_total M z hz inj a.val b.val
      (fun h => hne (Subtype.ext h))) ⟨positiveRootCell M,hroot⟩
    (fun a => positiveEarlier_root M z hz inj a.val)
  intro v hv
  have hv' : positiveCellTop M v.val ≠ 1 := by
    intro h
    apply hv
    exact Subtype.ext ((positiveCellTop_eq_one_iff M v.val).mp h)
  let a : NoncriticalPositiveCell M := ⟨v.val,hv'⟩
  by_cases hs : matchingLetter M z hz a ∈ a.val.2.val
  · let e := earlierLinkSubtypeIso (PositiveEarlier M z hz inj) D v (fun x => by
      have hh := (positiveEarlierLink_upper_iff M z hz inj a hs x.val).mp x.property
      exact hdown hh.1.le v.property)
    exact (weightHomeomorph e).contractibleSpace_iff.mpr
      ((weightHomeomorph (positiveEarlierLink_upper_iso M z hz inj a hs)).contractibleSpace_iff.mpr
        (hupper a v.property hs))
  · let b : D := ⟨(positiveMatch M z hz inj a).val,hmatch a v.property⟩
    have hab : v < b := positiveMatch_upper_lt M z hz inj a hs
    have hba : r b v := positiveMatch_before M z hz inj a hs
    let top : WeightEarlierLink r v := ⟨b,hba,Or.inr hab.le⟩
    have htop : ∀ x : WeightEarlierLink r v, x ≤ top := by
      intro x
      rcases x.property.2 with h|h
      · exact h.trans hab.le
      · have hne : v.val ≠ x.val.val := by
          intro he
          have hh := x.property.1
          change PositiveEarlier M z hz inj x.val.val v.val at hh
          rw [←he] at hh
          exact (positiveEarlier_wf M z hz inj).irrefl.irrefl _ hh
        obtain ⟨ha,_,he⟩ := positiveEarlier_upper_eq M z hz inj v.val x.val.val
          (lt_of_le_of_ne h hne) x.property.1
        change (x.val.val : PositiveCellPoset M inj) ≤ b.val
        exact le_of_eq he.symm
    let : OrderTop (WeightEarlierLink r v) := { top := top, le_top := htop }
    exact nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (nerve_orderTop_contractible (WeightEarlierLink r v))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FullSphericalCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] (M : CoxeterMatrix S)

omit [Fintype S] in
lemma right_minimum_of_longest_additive (R : Set S) (q : M.Group)
    (hq : IsParabolicLongest M R q) (w : M.Group)
    (hw : M.toCoxeterSystem.length (w*q) =
      M.toCoxeterSystem.length w + M.toCoxeterSystem.length q) :
    ∀ v : coxeterParabolic M R,
      M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length (w*v) := by
  intro v
  have hv : v.val⁻¹*q ∈ coxeterParabolic M R :=
    (coxeterParabolic M R).mul_mem ((coxeterParabolic M R).inv_mem v.property) hq.1
  have hb := hq.2 _ hv
  have hl := M.toCoxeterSystem.length_mul_le (w*v.val) (v.val⁻¹*q)
  have he : w*v.val*(v.val⁻¹*q) = w*q := by group
  rw [he,hw] at hl
  omega

theorem positiveCell_face_full_of_top_prefix [Finite M.Group]
    (a : PositiveLiftedCell M)
    (h : PositivePrefix M (positiveCellTop M a)
      (positiveSimpleLift M (sphericalLongest M (fullSphericalCell M).2))) :
    LiftedFace M (positiveCellToLifted M a) (fullSphericalCell M) := by
  have ht : positiveCellTop M a = positiveSimpleLift M (positiveToCoxeter M (positiveCellTop M a)) :=
    positivePrefix_of_simple_eq M h rfl
  have ha : a.1 = positiveSimpleLift M (positiveToCoxeter M a.1) :=
    (positive_simple_factors M a.1 (positiveSimpleLift M (sphericalLongest M a.2))
      (positiveToCoxeter M (positiveCellTop M a)) ht).1
  have hlen : M.toCoxeterSystem.length
      (positiveToCoxeter M a.1 * sphericalLongest M a.2) =
        M.toCoxeterSystem.length (positiveToCoxeter M a.1) +
          M.toCoxeterSystem.length (sphericalLongest M a.2) := by
    have hd := congrArg (positiveDegree M) ht
    simp only [positiveCellTop,map_mul,positiveToCoxeter_simpleLift,
      positiveDegree_mul,positiveDegree_simpleLift] at hd
    rw [ha,positiveDegree_simpleLift] at hd
    simpa only [positiveToCoxeter_simpleLift] using hd.symm
  let w := reducedExpression M (positiveToCoxeter M a.1)
  have hr := reducedExpression_reduced M (positiveToCoxeter M a.1)
  have he := wordCoxeter_reducedExpression M (positiveToCoxeter M a.1)
  refine ⟨Set.subset_univ _,w,(by intros; trivial),hr,?_,?_⟩
  · rw [he]
    exact right_minimum_of_longest_additive M a.2.val _ (sphericalLongest_spec M a.2) _ hlen
  · change positiveToArtin M a.1 = 1 * wordArtin M w
    rw [one_mul,ha,positiveToArtin_simpleLift,←he,positiveLift_word M w hr]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveFullCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveMatch_coatom (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) (b : PositiveCellPoset M inj)
    (hdb : positiveCellToLifted M (positiveMatch M z hz inj a).val ≤ positiveCellToLifted M b)
    (hba : positiveCellToLifted M b < positiveCellToLifted M a.val) :
    b = (positiveMatch M z hz inj a).val := by
  by_contra hne
  have hlt : positiveCellToLifted M (positiveMatch M z hz inj a).val < positiveCellToLifted M b :=
    lt_of_le_of_ne hdb (fun he => hne (positiveCellToLifted_injective M inj he).symm)
  have h1 := lifted_rank_strict M hlt
  have h2 := lifted_rank_strict M hba
  change (positiveMatch M z hz inj a).val.2.val.ncard < b.2.val.ncard at h1
  change b.2.val.ncard < a.val.2.val.ncard at h2
  rw [positiveMatch_type,matchingOtherType,ite_eq_left hs] at h1
  have hc := Set.ncard_sdiff_singleton_add_one hs (Set.toFinite a.val.2.val)
  omega

variable [Finite M.Group]

omit [LinearOrder S] in
lemma positiveFullCell_top : positiveCellTop M (positiveFullCell M) =
    positiveSimpleLift M (sphericalLongest M (fullSphericalCell M).2) := by
  exact one_mul _

omit [LinearOrder S] in
lemma positiveFullCell_noncritical (s : S) : positiveCellTop M (positiveFullCell M) ≠ 1 := by
  intro h
  have he := (positiveCellTop_eq_one_iff M _).mp h
  have ht := congrArg (fun a : PositiveLiftedCell M => a.2.val) he
  change (Set.univ : Set S) = ∅ at ht
  exact Set.notMem_empty s (ht ▸ Set.mem_univ s)

lemma positiveMatch_face_full (a : NoncriticalPositiveCell M)
    (h : positiveCellToLifted M a.val ≤ fullSphericalCell M) :
    positiveCellToLifted M (positiveMatch M z hz inj a).val ≤ fullSphericalCell M := by
  apply (lifted_le_iff_face M _ _).mpr
  apply positiveCell_face_full_of_top_prefix
  rw [positiveMatch_top,←positiveFullCell_top]
  apply positiveCellTop_prefix_of_face M inj
  rw [positiveFullCell_lifted]
  exact (lifted_le_iff_face M _ _).mp h

lemma positiveFullBoundary_down (hc : positiveCellTop M (positiveFullCell M) ≠ 1)
    {a b : PositiveCellPoset M inj} (hab : a ≤ b)
    (hb : positiveCellToLifted M b < fullSphericalCell M ∧
      b ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val) :
    positiveCellToLifted M a < fullSphericalCell M ∧
      a ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val := by
  change positiveCellToLifted M a ≤ positiveCellToLifted M b at hab
  refine ⟨hab.trans_lt hb.1,?_⟩
  intro he
  apply hb.2
  apply positiveMatch_coatom M z hz inj ⟨positiveFullCell M,hc⟩ (Set.mem_univ _) b
  · simpa only [he] using hab
  · simpa only [positiveFullCell_lifted] using hb.1

lemma positiveFullBoundary_match (hc : positiveCellTop M (positiveFullCell M) ≠ 1)
    (a : NoncriticalPositiveCell M)
    (ha : positiveCellToLifted M a.val < fullSphericalCell M ∧
      a.val ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val) :
    positiveCellToLifted M (positiveMatch M z hz inj a).val < fullSphericalCell M ∧
      (positiveMatch M z hz inj a).val ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val := by
  have hle := positiveMatch_face_full M z hz inj a ha.1.le
  refine ⟨lt_of_le_of_ne hle ?_,?_⟩
  · intro he
    have hm : (positiveMatch M z hz inj a).val = positiveFullCell M :=
      positiveCellToLifted_injective M inj (he.trans (positiveFullCell_lifted M).symm)
    exact ha.2 (positiveMatch_symm_value M z hz inj a ⟨positiveFullCell M,hc⟩ hm).symm
  · intro he
    have hh := congrArg (positiveMatch M z hz inj) (Subtype.ext he)
    rw [positiveMatch_involutive,positiveMatch_involutive] at hh
    have hh' := congrArg (fun a : NoncriticalPositiveCell M => positiveCellToLifted M a.val) hh
    rw [positiveFullCell_lifted] at hh'
    exact ha.1.ne hh'

lemma positiveFullBoundary_root (hc : positiveCellTop M (positiveFullCell M) ≠ 1) :
    positiveCellToLifted M (positiveRootCell M) < fullSphericalCell M ∧
      positiveRootCell M ≠ (positiveMatch M z hz inj ⟨positiveFullCell M,hc⟩).val := by
  have hr : positiveCellTop M (positiveRootCell M) = 1 := (positiveCellTop_eq_one_iff M _).mpr rfl
  have hle : positiveCellToLifted M (positiveRootCell M) ≤ fullSphericalCell M := by
    apply (lifted_le_iff_face M _ _).mpr
    apply positiveCell_face_full_of_top_prefix
    rw [hr]
    exact ⟨_,(one_mul _).symm⟩
  refine ⟨lt_of_le_of_ne hle ?_,?_⟩
  · intro he
    have hh := positiveCellToLifted_injective M inj (he.trans (positiveFullCell_lifted M).symm)
    exact hc (by rw [←hh,hr])
  · intro he
    have hh := positiveMatch_top M z hz inj ⟨positiveFullCell M,hc⟩
    rw [←he,hr] at hh
    exact hc hh.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveUpperBoundaryRank
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable

theorem positiveUpperBoundary_rank (n : ℕ) :
    ∀ {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
      (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
      (inj : Function.Injective (positiveToArtin M)) (a : NoncriticalPositiveCell M)
      (_ : matchingLetter M z hz a ∈ a.val.2.val) (_ : a.val.2.val.ncard = n),
    ContractibleSpace (OrderWeights {b : PositiveCellPoset M inj //
      positiveCellToLifted M b < positiveCellToLifted M a.val ∧
      b ≠ (positiveMatch M z hz inj a).val}) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S _ _ M z hz inj a hs hn
    let N := restrictedMatrix M a.val.2.val
    let : Finite N.Group := restricted_finite M a.val.2.val a.val.2.property
    obtain ⟨q,hq⟩ := exists_longest N.toCoxeterSystem
    let injN := spherical_positiveToArtin_injective M a.val.2.val a.val.2.property
    have hc : positiveCellTop N (positiveFullCell N) ≠ 1 :=
      positiveFullCell_noncritical N ⟨matchingLetter M z hz a,hs⟩
    let c : NoncriticalPositiveCell N := ⟨positiveFullCell N,hc⟩
    let D : Set (PositiveCellPoset N injN) := {b |
      positiveCellToLifted N b < fullSphericalCell N ∧ b ≠ (positiveMatch N q hq injN c).val}
    have hD : ContractibleSpace (OrderWeights D) := by
      apply invariantPositive_contractible N q hq injN D
        (positiveFullBoundary_root N q hq injN hc)
        (positiveFullBoundary_down N q hq injN hc)
        (positiveFullBoundary_match N q hq injN hc)
      intro b hb hbs
      have hk : b.val.2.val.ncard < n := by
        have hh := lifted_rank_strict N hb.1
        change b.val.2.val.ncard < (Set.univ : Set a.val.2.val).ncard at hh
        simpa only [Set.ncard_univ,Nat.card_coe_set_eq,hn] using hh
      exact ih b.val.2.val.ncard hk N q hq injN b hbs rfl
    let e := positiveUpperBoundaryRestrictionIso M z hz inj a hs q hq injN hc
    rw [positiveFullCell_lifted] at e
    exact (weightHomeomorph e).contractibleSpace_iff.mp hD

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

theorem positiveUpperBoundary_contractible (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) :
    ContractibleSpace (OrderWeights {b : PositiveCellPoset M inj //
      positiveCellToLifted M b < positiveCellToLifted M a.val ∧
      b ≠ (positiveMatch M z hz inj a).val}) :=
  positiveUpperBoundary_rank a.val.2.val.ncard M z hz inj a hs rfl

include z hz

theorem positiveCellPoset_contractible : ContractibleSpace (OrderWeights (PositiveCellPoset M inj)) := by
  apply orderWeights_contractible_of_earlier_links (PositiveEarlier M z hz inj)
    (positiveEarlier_wf M z hz inj) (positiveEarlier_total M z hz inj)
    (positiveRootCell M) (positiveEarlier_root M z hz inj)
  intro a ha
  have hn : positiveCellTop M a ≠ 1 := fun h => ha ((positiveCellTop_eq_one_iff M a).mp h)
  let c : NoncriticalPositiveCell M := ⟨a,hn⟩
  by_cases hs : matchingLetter M z hz c ∈ c.val.2.val
  · exact (weightHomeomorph (positiveEarlierLink_upper_iso M z hz inj c hs)).contractibleSpace_iff.mpr
      (positiveUpperBoundary_contractible M z hz inj c hs)
  · exact positiveEarlierLink_lower_contractible M z hz inj c hs

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_OrderWeightsContractibleLower2
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {P Q:Type u} [PartialOrder P] [PartialOrder Q]

theorem orderWeights_contractible_of_lower_preimages (f:P→oQ)
    (k:P→ℕ) (l:Q→ℕ) (N L:ℕ) (hk:∀p,k p≤N) (hl:∀q,l q≤L)
    (hkm:StrictMono k) (hlm:StrictMono l) (hQ:ContractibleSpace (OrderWeights Q))
    (hf:∀q,ContractibleSpace (OrderWeights {p:P // f p≤q})) :
    ContractibleSpace (OrderWeights P) := by
  let R:=OrderMappingCylinder f
  have hR:ContractibleSpace (OrderWeights R):=OrderMappingCylinder.weights_contractible f hQ
  have hF:∀v:R,v∉OrderMappingCylinder.old f →
      ContractibleSpace (OrderWeights {x:R // x∈OrderMappingCylinder.old f ∧ x<v}):=by
    intro v hv
    obtain ⟨q,rfl⟩:=(OrderMappingCylinder.not_old_iff f v).mp hv
    exact (weightHomeomorph (OrderMappingCylinder.oldLowerIso f q)).contractibleSpace_iff.mp (hf q)
  obtain ⟨r,hr⟩:=orderWeights_retract_of_lower_fibers (OrderMappingCylinder.old f)
    (OrderMappingCylinder.rank f k l N) (N+1+L)
    (OrderMappingCylinder.rank_bound f k l N L hk hl)
    (OrderMappingCylinder.rank_strict f k l N hk hkm hlm) hF
  have hA:ContractibleSpace (OrderWeights (OrderMappingCylinder.old f)):=
    contractible_of_continuous_retract
      ⟨weightMap (weightInclusion (OrderMappingCylinder.old f)),weightMap_continuous _⟩ r hr hR
  exact (weightHomeomorph (OrderMappingCylinder.oldIso f)).contractibleSpace_iff.mpr hA

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TypedRightCoset
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
attribute [-simp] _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S:Type u} (M:CoxeterMatrix S)

lemma deligne_same_type_eq {P Q:Deligne M} (h:P≤Q) (ht:P.val.1=Q.val.1) : P=Q := by
  obtain ⟨x,hx⟩:=P.property.2
  obtain ⟨y,hy⟩:=Q.property.2
  have hxm:x∈P.val.2:=by rw [hx];change x*x⁻¹∈artinParabolic M P.val.1;simp
  have hxy:x*y⁻¹∈artinParabolic M Q.val.1:=by simpa [hy,rightCoset] using h.2 hxm
  apply Subtype.ext
  apply Prod.ext ht
  apply Set.Subset.antisymm h.2
  intro z hz
  rw [hx]
  change z*x⁻¹∈artinParabolic M P.val.1
  rw [ht]
  have hzy:z*y⁻¹∈artinParabolic M Q.val.1:=by simpa [hy,rightCoset] using hz
  have hh:=(artinParabolic M Q.val.1).mul_mem hzy ((artinParabolic M Q.val.1).inv_mem hxy)
  simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left] using hh

lemma deligne_type_strict {P Q:Deligne M} (h:P<Q) : P.val.1⊂Q.val.1 :=
  lt_of_le_of_ne h.le.1 (fun he=>h.ne (deligne_same_type_eq M h.le he))

lemma deligne_card_strict [Finite S] : StrictMono (fun P:Deligne M=>P.val.1.ncard) := by
  intro P Q h
  exact Set.ncard_lt_ncard (deligne_type_strict M h) (Set.toFinite _)

theorem salvetti_cover_contractible_of_spherical_fibers [Finite S]
    (h:∀T:Set S,IsSpherical M T → ContractibleSpace (OrderWeights (SphericalLiftedFiber M T))) :
    ContractibleSpace (SalvettiCover M) := by
  have hd:ContractibleSpace (OrderWeights (Deligne M)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (deligne_contractible M)
  have hf:∀P:Deligne M,ContractibleSpace (OrderWeights {a:LiftedCell M // cellToDeligneOrderHom M a≤P}):=by
    intro P
    obtain ⟨x,hx⟩:=P.property.2
    have he:P=typedRightCoset M P.val.1 P.property.1 x:=by apply Subtype.ext;exact Prod.ext rfl hx
    rw [he]
    exact (weightHomeomorph (liftedLowerFiberIso M _ _ x)).contractibleSpace_iff.mpr (h _ P.property.1)
  have hc:ContractibleSpace (OrderWeights (LiftedCell M)):=
    orderWeights_contractible_of_lower_preimages (cellToDeligneOrderHom M)
      (fun a=>a.2.val.ncard) (fun P=>P.val.1.ncard) (Nat.card S) (Nat.card S)
      (lifted_rank_bound M) (fun _=>Set.ncard_le_card _) (lifted_rank_strict M)
      (deligne_card_strict M) hd hf
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mpr hc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_DirectedCoverSequence
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P I : Type} [PartialOrder P] [Countable I] [Nonempty I]

omit [PartialOrder P] in
lemma directed_cover_sequence (A : I → Set P)
    (hd : ∀ i j, ∃ k, A i ⊆ A k ∧ A j ⊆ A k) :
    ∃ c : ℕ → I, Monotone (fun n => A (c n)) ∧ ∀ i, ∃ n, A i ⊆ A (c n) := by
  obtain ⟨e,he⟩ := exists_surjective_nat I
  let upper : I → I → I := fun i j => (hd i j).choose
  have hu : ∀ i j, A i ⊆ A (upper i j) ∧ A j ⊆ A (upper i j) :=
    fun i j => (hd i j).choose_spec
  let c : ℕ → I := Nat.rec (e 0) (fun n i => upper i (e (n+1)))
  have hc0 : c 0 = e 0 := rfl
  have hcs : ∀ n, c (n+1) = upper (c n) (e (n+1)) := fun _ => rfl
  have hcm : Monotone (fun n => A (c n)) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hcs n]
    exact (hu _ _).1
  refine ⟨c,hcm,?_⟩
  intro i
  obtain ⟨n,rfl⟩ := he i
  refine ⟨n,?_⟩
  cases n with
  | zero => rw [hc0]
  | succ n => rw [hcs n]; exact (hu _ _).2

theorem orderWeights_contractible_of_countable_directed_cover
    (A : I → Set P) (hd : ∀ i j, ∃ k, A i ⊆ A k ∧ A j ⊆ A k)
    (hc : ∀ p, ∃ i, p ∈ A i)
    (hdown : ∀ i {p q}, p ≤ q → q ∈ A i → p ∈ A i)
    (hA : ∀ i, ContractibleSpace (OrderWeights (A i)))
    (k : P → ℕ) (N : ℕ) (hk : ∀ p, k p ≤ N) (hkm : StrictMono k) :
    ContractibleSpace (OrderWeights P) := by
  obtain ⟨c,hcm,hcf⟩ := directed_cover_sequence A hd
  let B : ℕ → Set P := fun n => A (c n)
  have hB : ∀ p, ∃ n, p ∈ B n := by
    intro p
    obtain ⟨i,hi⟩ := hc p
    obtain ⟨n,hn⟩ := hcf i
    exact ⟨n,hn hi⟩
  let f : P →o ℕ := {
    toFun := fun p => Nat.find (hB p)
    monotone' := by
      intro p q hpq
      apply Nat.find_min'
      exact hdown _ hpq (Nat.find_spec (hB q)) }
  have hf : ∀ p n, f p ≤ n ↔ p ∈ B n := by
    intro p n
    constructor
    · intro h
      exact hcm h (Nat.find_spec (hB p))
    · intro h
      exact Nat.find_min' (hB p) h
  apply orderWeights_contractible_of_natural_preimages f k N hk hkm
  intro n
  let e : {p : P // f p ≤ n} ≃o B n := {
    toFun := fun p => ⟨p.val,(hf p.val n).mp p.property⟩
    invFun := fun p => ⟨p.val,(hf p.val n).mpr p.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by intros; rfl }
  exact (weightHomeomorph e).contractibleSpace_iff.mpr (hA (c n))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_RestrictedLiftedContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

theorem restricted_lifted_contractible (T : Set S) (hT : IsSpherical M T) :
    ContractibleSpace (OrderWeights (LiftedCell (restrictedMatrix M T))) := by
  let N := restrictedMatrix M T
  let : Finite N.Group := restricted_finite M T hT
  let : Countable (Artin N) :=
    Function.Surjective.countable (PresentedGroup.mk_surjective (braidRelators N))
  obtain ⟨z,hz⟩ := exists_longest N.toCoxeterSystem
  let inj := spherical_positiveToArtin_injective M T hT
  have hpos : ContractibleSpace (OrderWeights (PositiveRegion N 1)) :=
    (weightHomeomorph (positiveCellRegionIso N inj)).contractibleSpace_iff.mp
      (positiveCellPoset_contractible N z hz inj)
  apply orderWeights_contractible_of_countable_directed_cover (PositiveRegion N)
    (spherical_positiveRegions_directed M T hT) (fun a => ⟨a.1,1,by simp⟩)
    (positiveRegion_face_closed N)
    (fun g => (weightHomeomorph (positiveRegionDeckIso N g)).contractibleSpace_iff.mp hpos)
    (fun a => a.2.val.ncard) (Nat.card T) (lifted_rank_bound N) (lifted_rank_strict N)

theorem sphericalLiftedFiber_contractible (T : Set S) (hT : IsSpherical M T) :
    ContractibleSpace (OrderWeights (SphericalLiftedFiber M T)) :=
  (weightHomeomorph (restrictedLiftedFiberIso M T hT)).contractibleSpace_iff.mp
    (restricted_lifted_contractible M T hT)

theorem source_salvetti_cover_contractible : ContractibleSpace (SalvettiCover M) :=
  salvetti_cover_contractible_of_spherical_fibers M (sphericalLiftedFiber_contractible M)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_SalvettiCoverContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

theorem salvetti_cover_contractible_oai [Finite S] (M : CoxeterMatrix S) : ContractibleSpace (SalvettiCover M) := by
  let := Fintype.ofFinite S
  let e := Fintype.equivFin S
  have hc : ContractibleSpace (OrderWeights (LiftedCell (M.reindex e))) :=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (source_salvetti_cover_contractible (M.reindex e))
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    ((weightHomeomorph (liftedReindex M e)).contractibleSpace_iff.mpr hc)

end HarmonicArtin

end OAI
end

theorem solution.{u} : type_of% @OAI.HarmonicArtin.salvetti_cover_contractible_oai.{u} := @OAI.HarmonicArtin.salvetti_cover_contractible_oai.{u}
