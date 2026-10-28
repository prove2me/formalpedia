-- Prove2me | solution 1 for OAI.Kadison.CompactInvariant.exists_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:10:57.51076+00:00
-- url     : https://prove2.me/submissions/0192fd3a-0fe8-432d-abf8-5abf50bab200

import Mathlib
import Definitions.Def_OAIQ039C004
import Theorems.Thm_OAI_Kadison_CompactInvariant_minimal_norm_compact

section
-- module Solutions.OAIQ039_CM.Commutator_CompactInvariant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Set

namespace Kadison.CompactInvariant

variable {G E : Type*} [Monoid G] [TopologicalSpace E] [T2Space E] [MulAction G E]

omit [TopologicalSpace E] [T2Space E] in
lemma invariant_sInter {F : Set (Set E)} (hF : ∀ S∈F,Invariant (G:=G) S) :
    Invariant (G:=G) (⋂₀ F) := by
  intro g x hx
  exact fun S hS => hF S hS g x (hx S hS)

theorem exists_minimal {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : Invariant (G:=G) C) (P : Set E → Prop) (hP : P C)
    (hPi : ∀ F : Set (Set E),F.Nonempty → (∀ S∈F,P S) → P (⋂₀ F)) :
    ∃ K : Set E,Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧
      Invariant (G:=G) S ∧ P S) K := by
  apply zorn_superset
  intro F hFC hF
  obtain rfl | hFn := F.eq_empty_or_nonempty
  · exact ⟨C,⟨subset_rfl,hne,hC.isClosed,hinv,hP⟩,by simp⟩
  have hsub : ⋂₀ F⊆C := by
    obtain ⟨S,hS⟩ := hFn
    exact (sInter_subset_of_mem hS).trans (hFC hS).1
  have hneI : (⋂₀ F).Nonempty := by
    have : Nonempty F := hFn.to_subtype
    rw [sInter_eq_iInter]
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · intro S T
      obtain hST | hTS := hF.total S.property T.property
      · exact ⟨S,subset_rfl,hST⟩
      · exact ⟨T,hTS,subset_rfl⟩
    · exact fun S => (hFC S.property).2.1
    · exact fun S => hC.of_isClosed_subset (hFC S.property).2.2.1 (hFC S.property).1
    · exact fun S => (hFC S.property).2.2.1
  refine ⟨⋂₀ F,⟨hsub,hneI,isClosed_sInter (fun S hS => (hFC hS).2.2.1),
    invariant_sInter (fun S hS => (hFC hS).2.2.2.1),hPi F hFn (fun S hS => (hFC hS).2.2.2.2)⟩,?_⟩
  exact fun S hS => sInter_subset_of_mem hS

lemma exists_minimal_compact {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : Invariant (G:=G) C) :
    ∃ K : Set E,Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧
      Invariant (G:=G) S) K := by
  obtain ⟨K,hK⟩ := exists_minimal hC hne hinv (fun _ => True) trivial (by simp)
  refine ⟨K,⟨⟨hK.prop.1,hK.prop.2.1,hK.prop.2.2.1,hK.prop.2.2.2.1⟩,?_⟩⟩
  intro S hS hSK
  exact hK.le_of_le ⟨hS.1,hS.2.1,hS.2.2.1,hS.2.2.2,trivial⟩ hSK

variable [AddCommGroup E] [Module ℝ E]

lemma exists_minimal_convex {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : Invariant (G:=G) C) (hconv : Convex ℝ C) :
    ∃ K : Set E,Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧
      Invariant (G:=G) S ∧ Convex ℝ S) K :=
  exists_minimal hC hne hinv (Convex ℝ) hconv (fun _ _ h => convex_sInter h)

end Kadison.CompactInvariant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DeMarrCenter
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Set

open scoped BigOperators

namespace Kadison.DeMarrCenter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_center {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (D : ℝ) (hD : 0<D) (hdiam : ∀ x∈K,∀ y∈K,dist x y≤D) :
    ∃ c∈convexHull ℝ K,∃ r : ℝ,0 ≤ r ∧ r<D ∧ ∀ x∈K,dist c x ≤ r := by
  classical
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball (x:E) (D/2))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,by simpa only [Metric.mem_ball,dist_self] using half_pos hD⟩)
  have htn : t.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨i,hi,_⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨i,hi⟩
  have hcard : 0<(t.card : ℝ) := by exact_mod_cast htn.card_pos
  let c : E := (t.card : ℝ)⁻¹ • ∑ i∈t,(i:E)
  let r : ℝ := (t.card : ℝ)⁻¹*(D/2+((t.erase htn.choose).card : ℝ)*D)
  have herase (i : K) (hi : i∈t) : ((t.erase i).card : ℝ)=(t.card : ℝ)-1 := by
    have hc := Finset.card_erase_add_one hi
    have hc' : ((t.erase i).card : ℝ)+1=(t.card : ℝ) := by exact_mod_cast hc
    linarith
  have hcent : c∈convexHull ℝ K := by
    have hh := t.centerMass_mem_convexHull (R:=ℝ) (s:=K) (w:=fun _ => (1:ℝ))
      (fun _ _ => zero_le_one) (by simpa only [Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one] using hcard)
      (fun i _ => i.property)
    simpa only [Finset.centerMass,Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one,one_smul] using hh
  have hr : 0 ≤ r := mul_nonneg (inv_nonneg.mpr hcard.le)
    (add_nonneg (half_pos hD).le (mul_nonneg (Nat.cast_nonneg _) hD.le))
  have hrD : r<D := by
    dsimp [r]
    rw [herase _ htn.choose_spec]
    apply (inv_mul_lt_iff₀ hcard).mpr
    nlinarith
  refine ⟨c,hcent,r,hr,hrD,?_⟩
  intro x hx
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (ht hx)
  have hid : dist (i:E) x≤D/2 := by
    rw [dist_comm]
    exact hxi.le
  have hs : ∑ j∈t,dist (j:E) x≤D/2+((t.erase i).card : ℝ)*D := by
    rw [←Finset.sum_erase_add _ _ hi]
    have hb : ∑ j∈t.erase i,dist (j:E) x≤((t.erase i).card : ℝ)*D := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        (Finset.sum_le_sum (s:=t.erase i) (fun j _ => hdiam j j.property x hx))
    linarith
  have hcx : c-x=(t.card : ℝ)⁻¹ • ∑ j∈t,((j:E)-x) := by
    rw [Finset.sum_sub_distrib,smul_sub,Finset.sum_const,← Nat.cast_smul_eq_nsmul ℝ]
    dsimp [c]
    rw [smul_smul,inv_mul_cancel₀ hcard.ne',one_smul]
  rw [dist_eq_norm,hcx,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hcard)]
  calc
    _ ≤ (t.card : ℝ)⁻¹*∑ j∈t,‖(j:E)-x‖ := mul_le_mul_of_nonneg_left
      (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
    _ ≤ (t.card : ℝ)⁻¹*(D/2+((t.erase i).card : ℝ)*D) := by
      simp only [←dist_eq_norm]
      exact mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hcard.le)
    _ = r := by dsimp [r]; rw [herase i hi,herase _ htn.choose_spec]

end Kadison.DeMarrCenter

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormSeparableFixedPoint
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Set TopologicalSpace

namespace Kadison.CompactInvariant

variable {G X E : Type*} [Group G] [TopologicalSpace X] [T2Space X]
  [AddCommGroup X] [Module ℝ X] [MulAction G X] [ContinuousConstSMul G X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixed_point_oai (j : X ≃ₗ[ℝ] E) (hj : Continuous j.symm)
    (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y ≤ r})
    (hiso : ∀ g : G,∀ x y : X,dist (j (g • x)) (j (g • y))=dist (j x) (j y))
    {C : Set X} (hcomp : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hinv : Invariant (G:=G) C) (hsep : IsSeparable (j '' C)) :
    ∃ x∈C,∀ g : G,g • x=x := by
  classical
  obtain ⟨C₀,hC₀⟩ := exists_minimal_convex hcomp hne hinv hconv
  have hCcomp : IsCompact C₀ := hcomp.of_isClosed_subset hC₀.prop.2.2.1 hC₀.prop.1
  obtain ⟨K,hK⟩ := exists_minimal_compact hCcomp hC₀.prop.2.1 hC₀.prop.2.2.2.1
  have hKcomp : IsCompact K := hCcomp.of_isClosed_subset hK.prop.2.2.1 hK.prop.1
  have hnormcomp : IsCompact (j '' K) := minimal_norm_compact j.toEquiv hj hball hiso
    hKcomp hK (hsep.mono (image_mono (hK.prop.1.trans hC₀.prop.1)))
  have hsubsingleton : (j '' K).Subsingleton := by
    by_contra hnot
    have hnontriv : (j '' K).Nontrivial := Set.not_subsingleton_iff.mp hnot
    let D := Metric.diam (j '' K)
    have hD : 0<D := Metric.diam_pos hnontriv hnormcomp.isBounded
    have hdiam : ∀ x∈j '' K,∀ y∈j '' K,dist x y≤D :=
      fun _ hx _ hy => Metric.dist_le_diam_of_mem hnormcomp.isBounded hx hy
    obtain ⟨c,hc,r,hr,hrD,hcr⟩ := DeMarrCenter.exists_center hnormcomp
      (hK.prop.2.1.image j) D hD hdiam
    have hcin : j.symm c∈C₀ := by
      change c∈convexHull ℝ (j.toLinearMap '' K) at hc
      rw [←j.toLinearMap.image_convexHull] at hc
      obtain ⟨z,hz,rfl⟩ := hc
      change j.symm (j z)∈C₀
      rw [j.symm_apply_apply]
      exact convexHull_min hK.prop.1 hC₀.prop.2.2.2.2 hz
    let L : Set X := C₀∩⋂ x∈K,j ⁻¹' Metric.closedBall (j x) r
    have hLc : IsClosed L := hC₀.prop.2.2.1.inter (isClosed_iInter fun x =>
      isClosed_iInter fun _ => hball (j x) r)
    have hLconv : Convex ℝ L := hC₀.prop.2.2.2.2.inter (convex_iInter fun x =>
      convex_iInter fun _ => (convex_closedBall (j x) r).linear_preimage j.toLinearMap)
    have hLne : L.Nonempty := by
      refine ⟨j.symm c,hcin,?_⟩
      apply mem_iInter₂.mpr
      intro x hx
      change dist (j (j.symm c)) (j x) ≤ r
      rw [j.apply_symm_apply]
      exact hcr _ ⟨x,hx,rfl⟩
    have hLinv : Invariant (G:=G) L := by
      intro g z hz
      refine ⟨hC₀.prop.2.2.2.1 g z hz.1,mem_iInter₂.mpr ?_⟩
      intro x hx
      have hgi : g⁻¹ • x∈K := hK.prop.2.2.2 g⁻¹ x hx
      have hb : dist (j z) (j (g⁻¹ • x)) ≤ r := mem_iInter₂.mp hz.2 _ hgi
      change dist (j (g • z)) (j x) ≤ r
      rw [←hiso g z (g⁻¹ • x),smul_inv_smul] at hb
      exact hb
    have hCL : C₀⊆L := hC₀.le_of_le
      ⟨(inter_subset_left.trans hC₀.prop.1),hLne,hLc,hLinv,hLconv⟩ inter_subset_left
    have hDle : D ≤ r := by
      apply Metric.diam_le_of_forall_dist_le hr
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      exact mem_iInter₂.mp (hCL (hK.prop.1 hx)).2 y hy
    linarith
  obtain ⟨x,hx⟩ := hK.prop.2.1
  refine ⟨x,hC₀.prop.1 (hK.prop.1 hx),?_⟩
  intro g
  apply j.injective
  exact hsubsingleton ⟨g • x,hK.prop.2.2.2 g x hx,rfl⟩ ⟨x,hx,rfl⟩

end Kadison.CompactInvariant

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.CompactInvariant.exists_fixed_point_oai.{u_1, u_2, u_3} := @OAI.Kadison.CompactInvariant.exists_fixed_point_oai.{u_1, u_2, u_3}
