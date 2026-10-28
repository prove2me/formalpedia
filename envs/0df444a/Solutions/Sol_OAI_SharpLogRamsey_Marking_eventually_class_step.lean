-- Prove2me | solution 1 for OAI.SharpLogRamsey.Marking.eventually_class_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:34:46.691933+00:00
-- url     : https://prove2.me/submissions/5598721e-aee7-4bf1-8083-507219028341

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_ActualPivot_eventually_reciprocal_message_cost
import Theorems.Thm_OAI_SharpLogRamsey_ActualPivot_supplied_book
import Theorems.Thm_OAI_SharpLogRamsey_Marking_eventually_high_ordered
import Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_eventually_integer_output
import Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_eventually_open_output

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem entropy_subadditive (p : Law (α × β)) : entropy p ≤ entropy p.fst+entropy p.snd := by
  have h := mutualInfo_nonneg p
  unfold mutualInfo at h
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem Law.le_map (p : Law α) (f : α → β) (a : α) :
    p.mass a ≤ (p.map f).mass (f a) := by
  apply single_le_sum (fun b hb => p.nonneg b)
  simp

end SharpLogRamsey.Selection
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_DivergenceMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Law.absContinuous_pi (p : Law (ι → β)) :
    p.AbsolutelyContinuous (Law.pi p.marginal) := by
  intro x hz
  change (∏ i, (p.marginal i).mass (x i)) = 0 at hz
  obtain ⟨i,hi⟩ := (prod_eq_zero_iff).mp hz
  have hh : p.mass x ≤ (p.marginal i).mass (x i) := p.le_map (fun y => y i) x
  exact le_antisymm (hi.2 ▸ hh) (p.nonneg _)

theorem totalCorrelation_eq_divergence (p : Law (ι → β)) :
    totalCorrelation p = divergence p (Law.pi p.marginal) := by
  have pointwise (x : ι → β) :
      p.mass x*Real.log (p.mass x/(∏ i, (p.marginal i).mass (x i))) =
      p.mass x*Real.log (p.mass x)-∑ i, p.mass x*Real.log ((p.marginal i).mass (x i)) := by
    by_cases hz : p.mass x = 0
    · simp [hz]
    have hp : 0 < p.mass x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hz)
    have hm (i : ι) : 0 < (p.marginal i).mass (x i) := hp.trans_le (p.le_map _ x)
    rw [Real.log_div hz (prod_ne_zero_iff.mpr fun i hi => (hm i).ne'),
      Real.log_prod (fun i hi => (hm i).ne'),mul_sub,mul_sum]
  have hs : ∑ x, ∑ i, p.mass x*Real.log ((p.marginal i).mass (x i)) =
      ∑ i, ∑ b, (p.marginal i).mass b*Real.log ((p.marginal i).mass b) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    exact (p.sum_map (fun x => x i) (fun b => Real.log ((p.marginal i).mass b))).symm
  unfold divergence
  change _ = ∑ x, p.mass x*Real.log (p.mass x/(∏ i, (p.marginal i).mass (x i)))
  simp_rw [pointwise]
  rw [sum_sub_distrib,hs]
  unfold totalCorrelation entropy
  rw [sum_neg_distrib]
  ring

theorem totalCorrelation_nonneg (p : Law (ι → β)) : 0 ≤ totalCorrelation p := by
  rw [totalCorrelation_eq_divergence]
  exact divergence_nonneg _ _ p.absContinuous_pi

theorem entropy_subadditive_pi (p : Law (ι → β)) :
    entropy p ≤ ∑ i, entropy (p.marginal i) := by
  have h := totalCorrelation_nonneg p
  unfold totalCorrelation at h
  linarith

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RemainingEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.Selection
variable {Ω α Γ A : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype A]

lemma entropy_mapped_support (p : Law Ω) (F : Ω → α) (S : Finset α)
    (hS : ∀ x, p.mass x ≠ 0 → F x ∈ S) : entropy (p.map F) ≤ Real.log S.card := by
  apply entropy_le_log_card
  intro a ha
  by_contra hn
  obtain ⟨x,hx,rfl⟩ := p.map_support F a hn
  exact ha (hS x hx)

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω α Γ M ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι]

omit [Fintype Ω] [Fintype Γ] [Fintype M] in

lemma subset_budget_deficit (p : Law (ι → α)) (S : Finset ι) (J : ι → ℝ)
    (hJ : ∀ i, entropy (p.marginal i) ≤ J i) :
    0 ≤ (∑ i∈S, J i)-entropy (p.restrict S) ∧
    (∑ i∈S, J i)-entropy (p.restrict S) ≤ (∑ i, J i)-entropy p := by
  have hcap (T : Finset ι) : entropy (p.restrict T) ≤ ∑ i∈T, J i := by
    apply (entropy_subadditive_pi _).trans
    simp only [Law.marginal_restrict]
    rw [sum_subtype T (fun _ => Iff.rfl)]
    exact sum_le_sum (fun i _ => hJ i)
  let f := fun x : ι → α => ((fun i:S => x i),(fun i:↥(Sᶜ) => x i))
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    by_cases hi : i∈S
    · exact congr_fun (congrArg Prod.fst hxy) ⟨i,hi⟩
    · exact congr_fun (congrArg Prod.snd hxy) ⟨i,by simpa using hi⟩
  have h1 : (p.map f).fst=p.restrict S := by rw [←Law.map_fst,Law.map_map]; rfl
  have h2 : (p.map f).snd=p.restrict Sᶜ := by rw [←Law.map_snd,Law.map_map]; rfl
  have ht := entropy_subadditive (p.map f)
  rw [entropy_map_eq_of_injective p f hf,h1,h2] at ht
  have hs := sum_add_sum_compl S J
  exact ⟨sub_nonneg.mpr (hcap S),by linarith [hcap Sᶜ]⟩

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_OrderedClassLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Γ α β : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β]

omit [Fintype Γ] in
lemma Law.map_congr_support (p : Law Ω) (f g : Ω→α)
    (h : ∀ x,p.mass x≠0→f x=g x) : p.map f=p.map g := by
  ext y
  change (∑ x with f x=y,p.mass x)=(∑ x with g x=y,p.mass x)
  simp only [sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hx : p.mass x=0
  · simp only [hx,ite_self]
  · rw [h x hx]

omit [Fintype β] in

theorem ordered_cond_entropy {N m : ℕ} (p : Law Ω) (θ : Ω→Γ) (F : Ω→Fin N→α)
    (S : Γ→Finset (Fin N)) (hm : m≤N) (z : Γ)
    (hz : (p.map θ).mass z≠0) (hs : (S z).card=m) :
    entropy ((p.cond θ z).map (orderedTuple S hm θ F))=
      entropy (((p.cond θ z).map F).restrict (S z)) := by
  let e := (S z).orderIsoOfFin hs
  let relabel : (S z→α)→(Fin m→α) := fun f i=>f (e i)
  have hi : Function.Injective relabel := by
    intro f g h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun h j
  have he : (p.cond θ z).map (orderedTuple S hm θ F)=
      (((p.cond θ z).map F).restrict (S z)).map relabel := by
    rw [Law.restrict,Law.map_map,Law.map_map]
    apply Law.map_congr_support
    intro x hx
    have hxθ := (p.cond_support θ z hz x hx).2
    funext i
    simp only [orderedTuple,hxθ,chosenOrder,dite_eq_left hs,Function.comp_apply,relabel,e]
    rfl
  rw [he]
  exact entropy_map_eq_of_injective _ relabel hi

omit [Fintype β] in

theorem ordered_deficit {N m : ℕ} (p : Law Ω) (θ : Ω→Γ) (F : Ω→Fin N→α)
    (S : Γ→Finset (Fin N)) (hm : m≤N)
    (hs : ∀ z,(p.map θ).mass z≠0→(S z).card=m) (J : ℝ) :
    (∑ z,(p.map θ).mass z*((m:ℝ)*J-
      entropy ((p.cond θ z).map (orderedTuple S hm θ F))))=
      selectedDeficit p θ F S J := by
  unfold selectedDeficit
  apply sum_congr rfl
  intro z _
  by_cases hz : (p.map θ).mass z=0
  · simp only [hz,zero_mul]
  · rw [ordered_cond_entropy p θ F S hm z hz (hs z hz),hs z hz]
    congr!

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

omit [FiniteDimensional K V] in

lemma scanConsistent_ordered {N m : ℕ}
    (F : Fin N→ProjectivePair (K:=K) (V:=V))
    (hF : ScanConsistent ((List.ofFn F).map toScan)) (e : Fin m ↪o Fin N) :
    ScanConsistent ((List.ofFn (fun i=>F (e i))).map toScan) := by
  unfold ScanConsistent at hF ⊢
  rw [List.map_ofFn] at hF ⊢
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact List.pairwise_ofFn.mp hF (e.strictMono hij)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RestrictionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ α : Type} [Fintype Ω] [Fintype Θ] [Fintype α]

attribute [local instance] OAI.SharpLogRamsey.Selection.restrictionFinDec
lemma ordered_restriction_budget {N m : ℕ} (hm : m≤N)
    (p : Law Ω) (θ : Ω→Θ) (F : Ω→Fin N→α)
    (D : Θ→Fin N→Finset α) (J : ℝ)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (θ x) i)
    (hJ : ∀ z i,log (D z i).card≤J)
    (S : Θ→Finset (Fin N))
    (hcard : ∀ z,(p.map θ).mass z≠0→(S z).card=m) :
    (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map
      (orderedTuple S hm θ F))))≤
    ∑ z,(p.map θ).mass z*((N:ℝ)*J-entropy ((p.cond θ z).map F)) := by
  have hord : (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map
      (orderedTuple S hm θ F))))=selectedDeficit p θ F S J := by
    convert ordered_deficit p θ F S hm hcard J using 1
    all_goals try with_reducible_and_instances rfl
    congr!
  rw [hord]
  unfold selectedDeficit
  apply sum_le_sum
  intro z _
  by_cases hz : (p.map θ).mass z=0
  · simp only [hz,zero_mul,le_refl]
  · apply mul_le_mul_of_nonneg_left _ ((p.map θ).nonneg z)
    have hcap : ∀ i,entropy (((p.cond θ z).map F).marginal i)≤J := by
      intro i
      change entropy (((p.cond θ z).map F).map (fun f=>f i))≤J
      rw [Law.map_map]
      apply (entropy_mapped_support (p.cond θ z) (fun x=>F x i) (D z i) ?_).trans (hJ z i)
      intro x hx
      obtain ⟨hx,he⟩:=p.cond_support θ z hz x hx
      simpa only [←he] using hD x hx i
    have hh := (subset_budget_deficit ((p.cond θ z).map F) (S z) (fun _=>J) hcap).2
    simpa only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] using hh
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RestrictionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section

lemma count_injective_restriction {I J : Type} [Fintype I] [Fintype J]
    (e : I↪J) (P : J→Prop) :
    (univ.filter (fun i=>P (e i))).card≤(univ.filter P).card := by
  calc
    _ = ((univ.filter (fun i=>P (e i))).image e).card := by
      rw [card_image_of_injective _ e.injective]
    _ ≤ _ := card_le_card (by
      intro j hj
      obtain ⟨i,hi,rfl⟩:=mem_image.mp hj
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩)

variable {Ω Θ α : Type} [Fintype Ω] [Fintype Θ] [Fintype α]

lemma prefixSet_card {N m : ℕ} (hm : m≤N) : (prefixSet hm).card=m := by
  rw [prefixSet,card_image_of_injective _ (Fin.castLE_injective hm),card_univ,Fintype.card_fin]

lemma prefix_budget {N m : ℕ} (hm : m≤N)
    (p : Law Ω) (θ : Ω→Θ) (F : Ω→Fin N→α)
    (D : Θ→Fin N→Finset α) (J : ℝ)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (θ x) i)
    (hJ : ∀ z i,Real.log (D z i).card≤J) :
    (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map
      (orderedTuple (fun _=>prefixSet hm) hm θ F))))≤
    ∑ z,(p.map θ).mass z*((N:ℝ)*J-entropy ((p.cond θ z).map F)) := by
  convert ordered_restriction_budget hm p θ F D J hD hJ (fun _=>prefixSet hm)
    (fun _ _=>prefixSet_card hm) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals congr!
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection SharpLogRamsey.MomentBudgetBridge

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

end SharpLogRamsey.SourceScales
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_RawLowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.HighRankBudgets
open Filter Real
open scoped Topology BigOperators
noncomputable section

lemma row_size {q x : ℝ} (hq : 1≤q) (hx : 1≤x) :
    q*x ≤ (⌈q*x⌉₊:ℝ) ∧ (⌈q*x⌉₊:ℝ) ≤ 2*q*x := by
  have hqx : 1≤q*x := by nlinarith
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)⟩

end
end SharpLogRamsey.HighRankBudgets
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter HighRankBudgets
open scoped Topology BigOperators
noncomputable section

lemma density_positive : 0 < richDensity := by unfold richDensity; positivity
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter Selection HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section
variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}

lemma highPrefactor_pos (d : ℕ) : 0<highPrefactor d := by
  have hh:=density_positive
  unfold highPrefactor
  positivity

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReciprocalBands
open Real

lemma reflected_integer_band {d r : ℕ} (hr : r≤d+1) {σ K u : ℝ}
    (h : IntegerBand r σ K u) :
    IntegerBand (d+1-r) σ K (((d:ℝ)+1)*σ-u) := by
  unfold IntegerBand at h ⊢
  rw [Nat.cast_sub hr,Nat.cast_add,Nat.cast_one]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [show ((d:ℝ)+1)*σ-u-((d:ℝ)+1-r)*σ= -(u-r*σ) by ring,abs_neg]

lemma reflected_open_band {d r : ℕ} (hr : r≤d+2) {σ K u : ℝ}
    (h : OpenBand r σ K u) :
    OpenBand (d+2-r) σ K (((d:ℝ)+1)*σ-u) := by
  unfold OpenBand at h ⊢
  rw [Nat.cast_sub hr,Nat.cast_add,Nat.cast_ofNat]
  constructor <;> nlinarith [h.1,h.2]

end SharpLogRamsey.ReciprocalBands

namespace SharpLogRamsey.Marking
open Finset Selection ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma covectorDomain_mem (D : Finset (ProjectivePair (K:=K) (V:=V)))
    (f : ProjectivePair (K:=K) (V:=V)) : f.swap ∈covectorDomain D ↔ f∈D := by
  simp [covectorDomain]

lemma covectorDomain_card (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).card=D.card := card_map _

lemma covectorDomain_first (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).image Prod.fst=D.image Prod.snd := by
  ext a
  simp [covectorDomain]

lemma covectorDomain_second (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).image Prod.snd=D.image Prod.fst := by
  ext a
  simp [covectorDomain]

lemma covectorTuple_consistent {N : ℕ} (F : Fin N→ProjectivePair (K:=K) (V:=V))
    [FiniteDimensional K V]
    (h : ScanConsistent ((List.ofFn F).map toScan)) :
    ∀ (i j : Fin N),i<j→(covectorTuple F i).1.rep (covectorTuple F j).2.rep=0→
      (covectorTuple F j).1.rep (covectorTuple F i).2.rep=0 := by
  rw [List.map_ofFn] at h
  exact List.pairwise_ofFn.mp h

lemma covectorTuple_flag {ι : Type*} (F : ι→ProjectivePair (K:=K) (V:=V))
    (h : ∀ i,Incidence.Incident (F i).1 (F i).2) (i : ι) :
    (covectorTuple F i).1.rep (covectorTuple F i).2.rep=0 := h i

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem covectorDomain_reciprocal {d : ℕ} {gap : ℝ}
    (D : Finset (ProjectivePair (K:=K) (V:=V)))
    (integer : Bool) (r : Fin (d+1))
    (h : ValidSlotClass d gap D (.inl (integer,r))) :
    let r' := if integer then d+1-r.val else d+2-r.val
    1 ≤ r' ∧ r'≤d ∧ ∃ u : ℝ,
      Real.log (Nat.card K)≤u ∧ u≤(d:ℝ)*Real.log (Nat.card K) ∧
      (((covectorDomain D).image Prod.fst).card:ℝ)≤
        1024*Real.exp (((d:ℝ)+1)*Real.log (Nat.card K)-u) ∧
      (((covectorDomain D).image Prod.snd).card:ℝ)≤1024*Real.exp u ∧
      (if integer then IntegerBand r' (Real.log (Nat.card K)) gap u
        else 2 ≤ r' ∧ OpenBand r' (Real.log (Nat.card K)) gap u) := by
  obtain ⟨u,hlo,hhi,hA,hB,hr,hband⟩:=h
  have hrle : r.val≤d := by omega
  cases integer
  · simp only [Bool.false_eq_true,ite_false] at hband ⊢
    refine ⟨by omega,by omega,((d:ℝ)+1)*Real.log (Nat.card K)-u,?_,?_,?_,?_,
      by omega,reflected_open_band (by omega) hband.2⟩
    · nlinarith
    · nlinarith
    · rw [covectorDomain_first]
      convert hB using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      ring
    · rw [covectorDomain_second]
      exact hA
  · simp only [ite_true] at hband ⊢
    refine ⟨by omega,by omega,((d:ℝ)+1)*Real.log (Nat.card K)-u,?_,?_,?_,?_,
      reflected_integer_band (by omega) hband⟩
    · nlinarith
    · nlinarith
    · rw [covectorDomain_first]
      convert hB using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      ring
    · rw [covectorDomain_second]
      exact hA

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma covectorTuple_entropy (p : Law Ω)
    (F : Ω→ι→ProjectivePair (K:=K) (V:=V)) :
    entropy (p.map (fun x=>covectorTuple (F x)))=entropy (p.map F) := by
  rw [show (fun x=>covectorTuple (F x))=covectorTuple∘F from rfl,←Law.map_map]
  apply entropy_map_eq_of_injective
  intro f g he
  funext i
  exact Prod.swap_injective (congrFun he i)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_CostContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma eventually_monomial_le_power (C a b ε : ℝ) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x^b := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-b)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0:ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-b))*x^b := by rw [mul_assoc, ←rpow_add hx0]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hx.le (rpow_nonneg hx0.le _)

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Real
noncomputable section

lemma packing_bounds (m L : ℕ) (hL : 0 < L) (hm : 2*L ≤ m) :
    1 ≤ m/L ∧ (m/L)*L ≤ m ∧ (m:ℝ)/2 ≤ ((m/L)*L:ℕ) := by
  have hw : 1 ≤ m/L := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have hlt:=Nat.mod_lt m hL
  have he:=Nat.mod_add_div m L
  have hl:=(Nat.div_mul_le_self m L)
  refine ⟨hw,hl,?_⟩
  have hv : m ≤ 2*((m/L)*L) := by
    have hh : L ≤ (m/L)*L:=by nlinarith
    nlinarith
  have hv' : (m:ℝ) ≤ 2*((m/L)*L:ℕ):=by exact_mod_cast hv
  linarith

lemma packing_scales (m L : ℕ) {q σ η D c C : ℝ}
    (hq : 0 < q) (hσ : 0 < σ) (_ : 0 < D) (hc : 0 < c) (hC : 0 < C)
    (hL : 0 < L) (hm : 2*L ≤ m)
    (hmlo : c*q*σ^(1+η) ≤ m) (hmhi : (m:ℝ) ≤ C*q*σ^(1+η))
    (hLlo : q*D*σ^(η/2) ≤ L) (hLhi : (L:ℝ) ≤ C*q*D*σ^(η/2)) :
    1 ≤ m/L ∧ (m/L)*L ≤ m ∧ (m:ℝ)/2 ≤ ((m/L)*L:ℕ) ∧
    (c/(2*C))*σ^(1+η/2) ≤ (m/L:ℕ)*D ∧
    (m/L:ℕ)*D ≤ C*σ^(1+η/2) := by
  obtain ⟨hw,hpack,hhalf⟩:=packing_bounds m L hL hm
  have hp : 0 < σ^(η/2):=rpow_pos_of_pos hσ _
  have hr : σ^(1+η)=σ^(1+η/2)*σ^(η/2) := by
    rw [←rpow_add hσ]
    congr 1
    ring
  have hqP : 0 < q*σ^(η/2):=mul_pos hq hp
  have hw0 : (0:ℝ) ≤ (m/L:ℕ):=Nat.cast_nonneg _
  have hpcast : ((m/L)*L:ℕ)=(m/L:ℕ)*(L:ℝ):=by norm_cast
  have hlow : c*q*σ^(1+η) ≤ 2*(m/L:ℕ)*(L:ℝ) := by
    rw [hpcast] at hhalf
    linarith
  have hupp : (m/L:ℕ)*(q*D*σ^(η/2)) ≤ C*q*σ^(1+η) := by
    have hpc : (m/L:ℕ)*(L:ℝ) ≤ m:=by exact_mod_cast hpack
    exact (mul_le_mul_of_nonneg_left hLlo hw0).trans (hpc.trans hmhi)
  have hlarg := hlow.trans (mul_le_mul_of_nonneg_left hLhi (by positivity : (0:ℝ) ≤ 2*(m/L:ℕ)))
  rw [hr] at hupp hlarg
  have hi : (m/L:ℕ)*D ≤ C*σ^(1+η/2) := by
    apply (mul_le_mul_iff_right₀ hqP).mp
    nlinarith only [hupp]
  have hlo : (c/(2*C))*σ^(1+η/2) ≤ (m/L:ℕ)*D := by
    apply (mul_le_mul_iff_right₀ (mul_pos (by positivity : 0 < 2*C) hqP)).mp
    have he : (2*C*(q*σ^(η/2)))*((c/(2*C))*σ^(1+η/2))=
        c*q*(σ^(1+η/2)*σ^(η/2)) := by field_simp
    rw [he]
    nlinarith only [hlarg]
  exact ⟨hw,hpack,hhalf,hlo,hi⟩
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Real Filter SourceScales
open scoped Topology
noncomputable section

lemma rounded_window {x y : ℝ} (hx : 2 ≤ x) (hy : 2 ≤ y) (hyx : y ≤ x) :
    2 ≤ ⌈x⌉₊ ∧ 0 < ⌊y⌋₊ ∧ ⌊y⌋₊ ≤ ⌈x⌉₊ ∧
    y/2 ≤ (⌊y⌋₊:ℝ) ∧
    x ≤ (4*(⌈x⌉₊+⌊y⌋₊):ℕ) ∧ (4*(⌈x⌉₊+⌊y⌋₊):ℕ) ≤ 12*x := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hn := Nat.le_ceil x
  have hn' := Nat.ceil_lt_add_one hx0
  have hk := Nat.floor_le hy0
  have hk' := Nat.lt_floor_add_one y
  have hn2 : 2 ≤ ⌈x⌉₊ := by exact_mod_cast (show (2:ℝ) ≤ ⌈x⌉₊ by linarith)
  have hkpos : 0 < ⌊y⌋₊ := by exact_mod_cast (show (0:ℝ) < ⌊y⌋₊ by linarith)
  have hkn : ⌊y⌋₊ ≤ ⌈x⌉₊ := by exact_mod_cast (show (⌊y⌋₊:ℝ) ≤ ⌈x⌉₊ by linarith)
  refine ⟨hn2,hkpos,hkn,by linarith,?_,?_⟩ <;> push_cast <;> linarith

theorem eventually_reciprocal_windows (η c C : ℝ) (hη : 0 < η) (hηu : η ≤ 1)
    (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q D : ℝ) (m : ℕ) (integer : Bool),
      exp σ = q → σ^beta η ≤ D → D ≤ σ^(1-η/2) →
      c*q*σ^(1+η) ≤ (m:ℝ) → (m:ℝ) ≤ C*q*σ^(1+η) →
      let x := if integer then q*σ^(1+η/2) else q*D*σ^(η/2)
      let n := ⌈x⌉₊
      let k := ⌊q*D*σ^(3000*beta η)⌋₊
      let L := 4*(n+k)
      let w := m/L
      2 ≤ n ∧ 0 < k ∧ k ≤ n ∧ 1 ≤ w ∧ w*L ≤ m ∧ (m:ℝ)/2 ≤ (w*L:ℕ) ∧
      (1/2)*q*D*σ^(3000*beta η) ≤ (k:ℝ) ∧
      (w:ℝ)*D ≤ max C 12*σ^(1+η/2) ∧
      (w:ℝ) ≤ max C 12*σ^(1+η/2) ∧
      (if integer then q*σ^(1+η/2) ≤ (n:ℝ)
       else (c/(2*max C 12))*σ^(1+η/2) ≤ (w:ℝ)*D) ∧
      (L:ℝ) ≤ 12*q*σ^(1+η/2) := by
  have ht : Tendsto (fun σ : ℝ => σ^(η/2)) atTop atTop := tendsto_rpow_atTop (by positivity)
  filter_upwards [ht.eventually_ge_atTop (24/c), eventually_ge_atTop (1:ℝ)]
    with σ hlarge hσ q D m integer he hDl hDu hmlo hmhi
  have hσ0 : 0 < σ := lt_of_lt_of_le hη (hηu.trans hσ)
  have hb := beta_pos hη
  have hD : 1 ≤ D := (one_le_rpow hσ hb.le).trans hDl
  have hD0 : 0 < D := by linarith
  have hq0 : 0 < q := he ▸ exp_pos _
  have hq2 : 2 ≤ q := by
    have h := add_one_le_exp σ
    rw [he] at h
    linarith
  have h3000 : 0 ≤ 3000*beta η := by positivity
  have hpow3 : 1 ≤ σ^(3000*beta η) := one_le_rpow hσ h3000
  let x := if integer then q*σ^(1+η/2) else q*D*σ^(η/2)
  let y := q*D*σ^(3000*beta η)
  have hqD : 2 ≤ q*D := hq2.trans (le_mul_of_one_le_right hq0.le hD)
  have hy : 2 ≤ y := hqD.trans (le_mul_of_one_le_right (by positivity) hpow3)
  have hx : 2 ≤ x := by
    have ha := one_le_rpow hσ (show 0 ≤ η/2 by positivity)
    have hb := one_le_rpow hσ (show 0 ≤ 1+η/2 by positivity)
    cases integer
    · exact hqD.trans (le_mul_of_one_le_right (by positivity) ha)
    · exact hq2.trans (le_mul_of_one_le_right hq0.le hb)
  have hyx : y ≤ x := by
    have h3 : σ^(3000*beta η) ≤ σ^(η/2) := rpow_le_rpow_of_exponent_le hσ (by unfold beta; linarith)
    have h4 : σ^((1-η/2)+3000*beta η) ≤ σ^(1+η/2) :=
      rpow_le_rpow_of_exponent_le hσ (by unfold beta; linarith)
    cases integer
    · exact mul_le_mul_of_nonneg_left h3 (by positivity)
    · calc
        y ≤ q*(σ^(1-η/2))*σ^(3000*beta η) := by dsimp only [y]; gcongr
        _ = q*σ^((1-η/2)+3000*beta η) := by rw [mul_assoc, ←rpow_add hσ0]
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 hq0.le
  obtain ⟨hn,hk,hkn,hklo,hLlo,hLhi⟩ := rounded_window hx hy hyx
  let L := 4*(⌈x⌉₊+⌊y⌋₊)
  have hL : 0 < L := by dsimp only [L]; omega
  have hxup : x ≤ q*σ^(1+η/2) := by
    cases integer
    · change q*D*σ^(η/2) ≤ _
      calc
        _ ≤ q*σ^(1-η/2)*σ^(η/2) := by gcongr
        _ = q*σ := by rw [mul_assoc, ←rpow_add hσ0]; congr 1; convert rpow_one σ using 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          calc
            σ = σ^(1:ℝ) := (rpow_one _).symm
            _ ≤ _ := rpow_le_rpow_of_exponent_le hσ (by linarith)) hq0.le
    · exact le_rfl
  have hLup : (L:ℝ) ≤ 12*q*σ^(1+η/2) := by dsimp only [L]; nlinarith
  have hscale : 24*q*σ^(1+η/2) ≤ c*q*σ^(1+η) := by
    have hh := (div_le_iff₀ hc).mp hlarge
    have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg hq0.le (rpow_nonneg hσ0.le (1+η/2)))
    have hp : σ^(η/2)*σ^(1+η/2) = σ^(1+η) := by rw [←rpow_add hσ0]; congr 1; ring
    nlinarith [show c*q*(σ^(η/2)*σ^(1+η/2))=c*q*σ^(1+η) by rw [hp]]
  have hpack : 2*L ≤ m := by exact_mod_cast (show (2:ℝ)*L ≤ m by linarith)
  obtain ⟨hw,hwm,hh⟩ := packing_bounds m L hL hpack
  have hbase : q*D*σ^(η/2) ≤ (L:ℝ) := by
    have hb : q*D*σ^(η/2) ≤ x := by
      cases integer
      · rfl
      · change q*D*σ^(η/2) ≤ q*σ^(1+η/2)
        calc
          _ ≤ q*σ^(1-η/2)*σ^(η/2) := by gcongr
          _ ≤ _ := by
            rw [mul_assoc, ←rpow_add hσ0]
            exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hσ (by linarith)) hq0.le
    exact hb.trans hLlo
  have hwd : ((m/L:ℕ):ℝ)*D ≤ max C 12*σ^(1+η/2) := by
    have hu : ((m/L:ℕ):ℝ)*(q*D*σ^(η/2)) ≤ C*q*σ^(1+η) :=
      (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg _)).trans
        ((by exact_mod_cast hwm : ((m/L:ℕ):ℝ)*(L:ℝ) ≤ m).trans hmhi)
    have hp : σ^(1+η)=σ^(1+η/2)*σ^(η/2) := by rw [←rpow_add hσ0]; congr 1; ring
    rw [hp] at hu
    have hwa : ((m/L:ℕ):ℝ)*D ≤ C*σ^(1+η/2) := by
      apply (mul_le_mul_iff_right₀ (mul_pos hq0 (rpow_pos_of_pos hσ0 (η/2)))).mp
      nlinarith only [hu]
    exact hwa.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_nonneg hσ0.le _))
  dsimp only
  change _ ∧ _ ∧ _ ∧ 1 ≤ m/L ∧ (m/L)*L ≤ m ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hn,hk,hkn,hw,hwm,hh,by dsimp only [y] at hklo; linarith,hwd,?_,?_,hLup⟩
  · have hw0 : (0:ℝ) ≤ (m/L:ℕ) := Nat.cast_nonneg _
    nlinarith
  · cases integer
    · simp only [Bool.false_eq_true,ite_false]
      have hA : 0 < max C 12 := lt_of_lt_of_le hC (le_max_left _ _)
      have hmA : (m:ℝ) ≤ max C 12*q*σ^(1+η) := hmhi.trans (by gcongr; exact le_max_left _ _)
      have hLA : (L:ℝ) ≤ max C 12*q*D*σ^(η/2) := by
        have hh : (L:ℝ) ≤ 12*(q*D*σ^(η/2)) := hLhi
        calc
          _ ≤ _ := hh
          _ ≤ _ := by
            have hp := mul_le_mul_of_nonneg_right (le_max_right C 12)
              (by positivity : 0 ≤ q*D*σ^(η/2))
            nlinarith only [hp]
      exact (packing_scales m L hq0 hσ0 hD0 hc hA hL hpack hmlo hmA hbase hLA).2.2.2.1
    · simpa only [ite_true] using Nat.le_ceil (q*σ^(1+η/2))
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Real Filter SourceScales Selection.Windows
open scoped Topology
noncomputable section

theorem eventually_high_window (η c : ℝ) (hη : 0 < η) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D : ℝ, ∀ m : ℕ,
      exp σ=q → σ^beta η ≤ D → D ≤ σ^(1-η/2) → c*q*σ^(1+η) ≤ m →
      let n:=m/8
      let k:=⌊q*D*σ^(3000*beta η)⌋₊
      2 ≤ n ∧ 0 < k ∧ k ≤ n ∧ 4*(n+k) ≤ m ∧
      (m:ℝ) ≤ 8*(2*(n+k):ℕ) ∧ (m:ℝ)/64 ≤ ((n+k)/2:ℕ) ∧
      (1/2)*q*D*σ^(3000*beta η) ≤ (k:ℝ) := by
  have he : 1-η/2+3000*beta η < 1+η:=by unfold beta;linarith
  have hs:=eventually_monomial_le_power 16 (1-η/2+3000*beta η) (1+η) c he hc
  have hpow : Tendsto (fun σ : ℝ=>σ^(1+η)) atTop atTop:=tendsto_rpow_atTop (by linarith)
  filter_upwards [hs,hpow.eventually_ge_atTop (16/c),eventually_ge_atTop (1:ℝ)]
    with σ hsmall hlarge hσ q D m heq hDl hDu hm
  have hσ0 : 0 < σ:=by linarith
  have hq : 2 ≤ q:=by have hh:=add_one_le_exp σ;rw [heq] at hh;linarith
  have hq0 : 0 < q:=by linarith
  have hD : 1 ≤ D:=(one_le_rpow hσ (beta_pos hη).le).trans hDl
  have hp : 1 ≤ σ^(3000*beta η):=one_le_rpow hσ (by unfold beta;positivity)
  have hx : 2 ≤ q*D*σ^(3000*beta η):=
    (hq.trans (le_mul_of_one_le_right hq0.le hD)).trans
      (le_mul_of_one_le_right (by positivity) hp)
  have hmp : 16 ≤ m:=by
    have hh:=(div_le_iff₀ hc).mp hlarge
    have hh' := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ q by linarith)
      (by positivity : 0 ≤ c*σ^(1+η))
    exact_mod_cast (show (16:ℝ) ≤ m by nlinarith only [hm,hh,hh'])
  have hk : (⌊q*D*σ^(3000*beta η)⌋₊:ℝ) ≤ q*D*σ^(3000*beta η):=Nat.floor_le (by positivity)
  have hk' : 16*(⌊q*D*σ^(3000*beta η)⌋₊:ℝ) ≤ m:=by
    calc
      _ ≤ 16*(q*D*σ^(3000*beta η)):=by linarith only [hk]
      _ ≤ 16*(q*σ^(1-η/2)*σ^(3000*beta η)):=by gcongr
      _ = q*(16*σ^(1-η/2+3000*beta η)):=by rw [mul_assoc q,←rpow_add hσ0];ring
      _ ≤ q*(c*σ^(1+η)):=mul_le_mul_of_nonneg_left hsmall hq0.le
      _ ≤ _:=by nlinarith only [hm]
  have hkNat : 16*⌊q*D*σ^(3000*beta η)⌋₊ ≤ m:=by exact_mod_cast hk'
  obtain ⟨_,hkpos,_,hklo,_,_⟩:=rounded_window hx hx le_rfl
  dsimp only
  refine ⟨by omega,hkpos,by omega,by omega,?_,?_,?_⟩
  · exact_mod_cast (show m ≤ 8*(2*(m/8+⌊q*D*σ^(3000*beta η)⌋₊)) by omega)
  · have hh : m ≤ 64*((m/8+⌊q*D*σ^(3000*beta η)⌋₊)/2):=by omega
    have hh' : (m:ℝ) ≤ 64*((m/8+⌊q*D*σ^(3000*beta η)⌋₊)/2:ℕ):=by exact_mod_cast hh
    linarith
  · linarith only [hklo]

theorem eventually_high_cost (η c : ℝ) (d : ℕ) (hη : 0 < η) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D m : ℝ,
      exp σ=q → 1 ≤ D → c*q*σ^(1+η) ≤ m →
      4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ) ≤ D*σ^(-η/3)*m := by
  have hgap : beta η+1 < 1+2*η/3:=by unfold beta;linarith
  filter_upwards [eventually_monomial_le_power (8*((d:ℝ)+1)) (beta η+1)
    (1+2*η/3) c hgap hc,eventually_ge_atTop (1:ℝ)] with σ hs hσ q D m he hD hm
  have hσ0 : 0 < σ:=by linarith
  have hq0 : 0 < q:=he ▸ exp_pos _
  have hrow : (rawRows σ η:ℝ) ≤ 2*q*σ^beta η:=by
    simpa only [rawRows,HighRankBudgets.beta,SourceScales.beta,he] using
      (HighRankBudgets.row_size (one_le_exp hσ0.le) (one_le_rpow hσ (beta_pos hη).le)).2
  have hl : log (2:ℝ) ≤ σ:=
    (log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by linarith)
  have hlast:=mul_le_mul_of_nonneg_left hm (mul_nonneg (by linarith : 0 ≤ D)
    (rpow_nonneg hσ0.le (-η/3)))
  have hp : σ^(-η/3)*σ^(1+η)=σ^(1+2*η/3):=by rw [←rpow_add hσ0];congr 1;ring
  calc
    _ ≤ 4*(2*q*σ^beta η)*(((d:ℝ)+1)*σ):=by gcongr;linarith
    _ = (8*((d:ℝ)+1)*σ^(beta η+1))*q:=by rw [rpow_add hσ0,rpow_one];ring
    _ ≤ c*σ^(1+2*η/3)*q:=mul_le_mul_of_nonneg_right hs hq0.le
    _ ≤ D*(c*σ^(1+2*η/3)*q):=le_mul_of_one_le_left (by positivity) hD
    _ = D*σ^(-η/3)*(c*q*σ^(1+η)):=by
      linear_combination -(D*c*q)*hp
    _ ≤ _:=hlast

theorem eventually_high_domain (η : ℝ) (d : ℕ) (hη : 0 < η) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, 0 ≤ D →
      ((d:ℝ)+1)*scaleK σ η D ≤ 16*scaleKstar σ η D := by
  have ht:=tendsto_rpow_atTop (show 0 < 3*beta η by unfold beta;positivity)
  filter_upwards [ht.eventually_ge_atTop (((d:ℝ)+1)/16),eventually_gt_atTop (0:ℝ)]
    with σ hs hσ D hD
  have hh : (d:ℝ)+1 ≤ 16*σ^(3*beta η):=by linarith
  have hp : σ^(3*beta η)*σ^(3*beta η)=σ^(6*beta η):=by rw [←rpow_add hσ];congr 1;ring
  unfold scaleK scaleKstar
  have hk:=mul_le_mul_of_nonneg_right hh (mul_nonneg hD (rpow_nonneg hσ.le (3*beta η)))
  nlinarith only [hk,show 16*D*(σ^(3*beta η)*σ^(3*beta η))=16*D*σ^(6*beta η) by rw [hp]]
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.flat_ActualHighRankStep_3
attribute [local instance] OAI.SharpLogRamsey.Marking.flat_ActualHighRankStep_4
theorem eventually_high_step (η c C0 : ℝ) (hη : 0 < η) (hc : 0 < c) (hC0 : 0 < C0)
    (d : ℕ) (hd : 2 ≤ d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], exp σ=(q:ℝ) →
    ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ] (m : ℕ) (p : Law Ω) (θ : Ω→Θ)
      (F : Ω→Fin m→ProjectivePair (K:=ZMod q) (V:=Fin (d+1)→ZMod q))
      (S : Θ→Fin m→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (d+1)→ZMod q)))
      (D J budget : ℝ) (R : ℕ) (r r' : Fin (d+1)),
      Admissible σ η D R → c*(q:ℝ)*σ^(1+η) ≤ m → (d:ℝ)*σ ≤ J →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (θ x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ j,ValidSlotClass d (scaleKstar σ η D) (S (θ x) j) (.inr (r,r'))) →
      (∀ z j,((S z j).card:ℝ) ≤ 64*(q:ℝ)^d) →
      (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map F))) ≤ budget →
      budget ≤ C0*(m:ℝ)*D*σ^(-beta η) →
      ∃ m' : ℕ, (m:ℝ)/64 ≤ m' ∧
        Nonempty (ContextOutput p F m' (highPrefactor d*(q:ℝ)^d*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(m:ℝ)) 4) := by
  filter_upwards [eventually_high_window η c hη hc,
    eventually_high_cost η c d hη hc,eventually_high_domain η d hη,
    eventually_high_ordered hη d hd (8*C0) (1/2) (by positivity) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ hwin hcost hdom hout hσ
  intro q _ he Ω Θ _ _ m p θ F S D J budget R r r' had hmlo hJ hSJ hS hf hcon hclass hsize hbudget hb
  have hσ0 : 0 < σ:=by linarith
  have hD : 1 ≤ D:=(one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
  have hqlog : log (Nat.card (ZMod q):ℝ)=σ:=by rw [Nat.card_zmod,←he,log_exp]
  let n:=m/8
  let k:=⌊(q:ℝ)*D*σ^(3000*beta η)⌋₊
  obtain ⟨hn,hk,hkn,hwm,hmup,hmret,hklow⟩:=hwin (q:ℝ) D m he had.D_lower had.D_upper hmlo
  let T : Θ→Finset (Fin m):=fun _=>prefixSet hwm
  let e:=chosenOrder T hwm
  let G:=orderedTuple T hwm θ F
  let S':=fun z j=>S z (e z j)
  have hGS : ∀ z j,log (S' z j).card ≤ J:=fun z j=>hSJ z (e z j)
  have hG : ∀ x,p.mass x≠0→∀ j,G x j∈S' (θ x) j:=fun x hx j=>hS x hx (e (θ x) j)
  have hgf : ∀ x,p.mass x≠0→∀ j,Incidence.Incident (G x j).1 (G x j).2:=
    fun x hx j=>hf x hx (e (θ x) j)
  have hgcon : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan):=
    fun x hx=>scanConsistent_ordered (F x) (hcon x hx) (e (θ x))
  have hgclass : ∀ x,p.mass x≠0→∀ j,ValidSlotClass d (scaleKstar σ η D) (S' (θ x) j)
      (.inr (r,r')):=fun x hx j=>hclass x hx (e (θ x) j)
  have hgsize : ∀ z j,((S' z j).card:ℝ) ≤ 64*(Nat.card (ZMod q):ℝ)^d:=by
    intro z j
    simpa only [Nat.card_zmod] using hsize z (e z j)
  have hgbud : (∑ z,(p.map θ).mass z*((4*(n+k):ℕ)*J-
      entropy ((p.cond θ z).map G))) ≤ budget :=
    (prefix_budget hwm p θ F S J hS hSJ).trans hbudget
  have hbb : budget ≤ (8*C0)*(2*(n+k):ℕ)*D*σ^(-beta η) := by
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmup hC0.le)
      (mul_nonneg (by linarith : 0 ≤ D) (rpow_nonneg hσ0.le (-beta η)))
    nlinarith only [hb,hh]
  obtain ⟨out⟩:=hout (ZMod q) Ω Θ hqlog n k hn hk hkn p θ G S' D J budget
    (scaleKstar σ η D) r r' had.D_lower had.D_upper hJ hG hGS hgf hgcon hgclass hgsize
    hgbud hbb (by simpa only [Nat.card_zmod,HighRankBudgets.beta,SourceScales.beta,k] using hklow)
  have hB : highPrefactor d*(Nat.card (ZMod q):ℝ)^d*
      exp (((d:ℝ)+1)*HighRankBudgets.scaleK σ η D) ≤
      highPrefactor d*(q:ℝ)^d*exp (16*scaleKstar σ η D) := by
    rw [Nat.card_zmod]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr (hdom D (by linarith)))
    exact mul_nonneg (highPrefactor_pos d).le (pow_nonneg (Nat.cast_nonneg _) _)
  have hfinalcost:=hcost (q:ℝ) D (m:ℝ) he hD hmlo
  have out':=out.toContextOutput.mono hB hfinalcost (le_refl 4)
  have final:=out'.transport (Equiv.refl _) F (fun z=>e (θ z)) (fun _ _=>rfl)
  exact ⟨(n+k)/2,hmret,⟨final⟩⟩
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_PopulationSublist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section

lemma finProd_position {w n : ℕ} (i : Slot w n) :
    (finProdFinEquiv i).val=position i := by
  simp [finProdFinEquiv,position,Nat.mul_comm,Nat.add_comm]

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α Ω Θ : Type} [Fintype Ω] [Fintype Θ] [Fintype α]

omit [Fintype α] in
lemma flatten_window {w n : ℕ} (F : Fin (w*(4*n))→α) :
    flattenTuple (windowTuple F)=F := by
  funext i
  simp only [flattenTuple,windowTuple,Equiv.apply_symm_apply]

lemma window_entropy {w n : ℕ} (p : Law Ω) (F : Ω→Fin (w*(4*n))→α) :
    entropy (p.map (fun x=>windowTuple (F x)))=entropy (p.map F) := by
  rw [show (fun x=>windowTuple (F x))=windowTuple∘F from rfl,←Law.map_map]
  apply entropy_map_eq_of_injective
  intro f g h
  funext i
  have hh:=congrFun h (finProdFinEquiv.symm i)
  simpa only [windowTuple,Equiv.apply_symm_apply] using hh

end
end SharpLogRamsey.Selection.Windows

namespace SharpLogRamsey.Marking
open Finset Selection Selection.Windows ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype Ω] [Fintype Θ]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Fintype Θ] [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in

theorem reciprocal_parameters {N d : ℕ} (p : Law Ω) (θ : Ω→Θ)
    (S : Θ→Fin N→Finset (ProjectivePair (K:=K) (V:=V)))
    (integer : Bool) (r : Fin (d+1)) (gap : ℝ) (hN : 0<N)
    (hclass : ∀ x,p.mass x≠0→∀ i,ValidSlotClass d gap (S (θ x) i) (.inl (integer,r))) :
    let r':=if integer then d+1-r.val else d+2-r.val
    1 ≤ r' ∧ r'≤d ∧ ∃ u : Θ→Fin N→ℝ,∀ x,p.mass x≠0→∀ i,
      (((covectorDomain (S (θ x) i)).image Prod.fst).card:ℝ)≤
        1024*Real.exp (((d:ℝ)+1)*Real.log (Nat.card K)-u (θ x) i) ∧
      (((covectorDomain (S (θ x) i)).image Prod.snd).card:ℝ)≤1024*Real.exp (u (θ x) i) ∧
      (if integer then IntegerBand r' (Real.log (Nat.card K)) gap (u (θ x) i)
        else OpenBand r' (Real.log (Nat.card K)) gap (u (θ x) i)) := by
  have hpos : ∃ x,p.mass x≠0 := by
    by_contra hh
    have hz : ∀ x,p.mass x=0:=by simpa only [not_exists,not_not] using hh
    have hh:=p.total
    simp only [hz,sum_const_zero] at hh
    norm_num at hh
  obtain ⟨x,hx⟩:=hpos
  have hh:=covectorDomain_reciprocal (S (θ x) ⟨0,hN⟩) integer r (hclass x hx _)
  refine ⟨hh.1,hh.2.1,?_,?_⟩
  · exact fun z i=>if h : ValidSlotClass d gap (S z i) (.inl (integer,r)) then
      (covectorDomain_reciprocal (S z i) integer r h).2.2.choose else 0
  · intro x hx i
    simp only [dite_eq_left (hclass x hx i)]
    have huv:=(covectorDomain_reciprocal (S (θ x) i) integer r (hclass x hx i)).2.2.choose_spec
    refine ⟨huv.2.2.1,huv.2.2.2.1,?_⟩
    cases integer <;> simp only [Bool.false_eq_true,ite_false,ite_true] at huv ⊢
    · exact huv.2.2.2.2.2
    · exact huv.2.2.2.2
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalOrdered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section

theorem eventually_reciprocal_ordered (d : ℕ) (η C A C0 c : ℝ)
    (hη : 0<η) (hC : 0<C) (hC0 : 0≤C0) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (_ : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3)),
        0≤b → 0≤H → 4≤P → b+log 1000000≤P → 0≤τ → τ≤1/40000 →
      ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (F : Ω→Fin (w*(4*(n+k)))→ProjectivePair (K:=K) (V:=V))
        (S : Θ→Fin (w*(4*(n+k)))→Finset (ProjectivePair (K:=K) (V:=V)))
        (integer : Bool) (r : Fin (d+3)) (J M budget : ℝ),
        2≤n → 0<k → k≤n → (w:ℝ)≤C*σ^A → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
        (∀ z i,log (S z i).card≤J) →
        (∀ x,p.mass x≠0→∀ i,F x i∈S (θ x) i) →
        (∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2) →
        (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
        (∀ x,p.mass x≠0→∀ i,ValidSlotClass (d+2) (scaleKstar σ η D) (S (θ x) i) (.inl (integer,r))) →
        (∀ z i,((S z i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∑ z,(p.map θ).mass z*((w*(4*(n+k)):ℕ)*J-entropy ((p.cond θ z).map F)))≤budget →
        budget≤C0*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) →
        c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
        (if integer then
          M≤C0*σ ∧ c*(Nat.card K:ℝ)*σ^(1+η/2)≤n ∧
          ∀ x,p.mass x≠0→∀ W : Submodule K V,
            ((univ.filter (fun i : Slot w (n+k)=>
              (covectorTuple (F x) (finProdFinEquiv i))∈
                orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ)≤M
         else c*σ^(1+η/2)≤(w:ℝ)*D) →
        Nonempty (Fin w) →
        Nonempty (ContextOutput p F (w*(n+k)) (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
          (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
            w (Nat.log 2 w+1) (2*(n+k))) 2) := by
  filter_upwards [eventually_integer_output d η C A C0 c hη hC hC0 hc,
    eventually_open_output d η C A C0 c hη hC hC0 hc] with σ hi ho
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hb hH hP haP hτ hτsmall Ω Θ _ _ w n k p θ F S integer r J M budget hn hk hkn hw hJ hM hSJ hS hf hcon hclass hsize hbudget hb0 hk0 hcase hne
  obtain ⟨fallback⟩:=hne
  have hN : 0<w*(4*(n+k)) := by
    have hw : 0<w:=Nat.zero_lt_of_lt fallback.isLt
    positivity
  obtain ⟨hr1,hr,u,hu⟩:=reciprocal_parameters p θ S integer r _ hN hclass
  let G:=fun x=>windowTuple (covectorTuple (F x))
  let T:=fun z (i : Slot w (n+k))=>covectorDomain (S z (finProdFinEquiv i))
  let u':=fun z (i : Slot w (n+k))=>u z (finProdFinEquiv i)
  have hG : ∀ x,p.mass x≠0→∀ i,G x i∈T (θ x) i := by
    intro x hx i
    exact (covectorDomain_mem _ _).mpr (hS x hx _)
  have hT : ∀ z i,log (T z i).card≤J := by
    intro z i
    simpa only [T,covectorDomain_card] using hSJ z (finProdFinEquiv i)
  have hflag : ∀ x,p.mass x≠0→∀ i,(G x i).1.rep (G x i).2.rep=0 := by
    intro x hx i
    exact covectorTuple_flag (F x) (hf x hx) _
  have hchron : ∀ x,p.mass x≠0→∀ i j,position i<position j→
      (G x i).1.rep (G x j).2.rep=0→(G x j).1.rep (G x i).2.rep=0 := by
    intro x hx i j hij
    apply covectorTuple_consistent (F x) (hcon x hx)
    change (finProdFinEquiv i).val<(finProdFinEquiv j).val
    simpa only [finProd_position] using hij
  have hcap : ∀ x,p.mass x≠0→∀ i,
      (((T (θ x) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u' (θ x) i) ∧
      (((T (θ x) i).image Prod.snd).card:ℝ)≤1024*exp (u' (θ x) i) ∧
      ((T (θ x) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2) := by
    intro x hx i
    have huv:=hu x hx (finProdFinEquiv i)
    refine ⟨?_,?_,?_⟩
    · convert huv.1 using 1
      all_goals try with_reducible_and_instances rfl
      simp only [u',hlog,Nat.cast_add,Nat.cast_ofNat]
      ring_nf
    · simpa only [T,u'] using huv.2.1
    · simpa only [T,covectorDomain_card] using hsize (θ x) (finProdFinEquiv i)
  have hbud : (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget := by
    apply le_trans (le_of_eq ?_) hbudget
    apply sum_congr rfl
    intro z _
    dsimp only [G]
    rw [window_entropy]
    simp only [Slot,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    congr 2
    convert covectorTuple_entropy (p.cond θ z) F using 1 <;> congr!
  have hout : Nonempty (ContextOutput p (fun x=>flattenTuple (G x)) (w*(n+k))
      (8000000*(Nat.card K:ℝ)^(d+2)*exp (16*scaleKstar σ η D))
      (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=16*scaleKstar σ η D) (P:=P) (H:=H)
        w (Nat.log 2 w+1) (2*(n+k))) 2) := by
    cases integer
    · simp only [Bool.false_eq_true,ite_false] at hr hu hcase
      exact ho K V hdim hlog D P H hDl hDu book hb hH hP haP hτ hτsmall Ω Θ w n k p θ G T u'
        (d+4-r.val) J budget hn hk hkn hw hcase (by omega) hJ hT hG hflag hchron hcap
        (by intro x hx i;simpa only [u',hlog] using (hu x hx (finProdFinEquiv i)).2.2)
        hbud hb0 hk0 fallback
    · simp only [ite_true] at hr hu hcase
      exact hi K V hdim hlog D P H hDl hDu book hb hH hP haP hτ hτsmall Ω Θ w n k p θ G T u'
        (d+3-r.val) J M budget hn hk hkn hw (by omega) hJ hM hT hG hflag hchron hcap
        (by intro x hx i;simpa only [u',hlog] using (hu x hx (finProdFinEquiv i)).2.2)
        hcase.2.2 hbud hb0 hcase.1 hk0 hcase.2.1 fallback
  obtain ⟨e⟩:=hout
  exact ⟨e.transport (Equiv.prodComm _ _) F (fun _=>(OrderIso.refl _).toOrderEmbedding) (by
    intro x i
    simp only [G,flatten_window,covectorTuple,Equiv.prodComm_apply,Prod.swap_swap,
      OrderIso.coe_toOrderEmbedding,OrderIso.refl_apply])⟩
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section

 theorem eventually_reciprocal_step (i : ℕ) (η c C C0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C) (hC0 : 0 < C0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
      [Fintype (Projectivization (ZMod q) V)]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) V))]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Module.Dual (ZMod q) V)))],
      Module.finrank (ZMod q) V=i+4 →
    ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ] (m : ℕ) (p : Law Ω) (θ : Ω→Θ)
      (F : Ω→Fin m→ProjectivePair (K:=ZMod q) (V:=V))
      (S : Θ→Fin m→Finset (ProjectivePair (K:=ZMod q) (V:=V)))
      (D J M budget : ℝ) (R : ℕ) (integer : Bool) (r : Fin (i+4)),
      Admissible σ η D R → c*(q:ℝ)*σ^(1+η) ≤ m → (m:ℝ) ≤ C*q*σ^(1+η) →
      ((i+3:ℕ):ℝ)*σ ≤ J → 0 ≤ M → M ≤ C0*σ →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (θ x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ j,ValidSlotClass (i+3) (scaleKstar σ η D) (S (θ x) j) (.inl (integer,r))) →
      (∀ z j,((S z j).card:ℝ) ≤ 64*(q:ℝ)^(i+3)) →
      (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map F))) ≤ budget →
      budget ≤ C0*(m:ℝ)*D*σ^(-beta η) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) V,
        ((univ.filter (fun j : Fin m=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M) →
      ∃ w m' : ℕ, 1 ≤ w ∧ (w:ℝ)*D ≤ max C 12*σ^(1+η/2) ∧ (m:ℝ)/8 ≤ m' ∧
        Nonempty (ContextOutput p F m' (8000000*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(m:ℝ)) 2) := by
  obtain ⟨H,hH,hbook⟩:=supplied_book i
  let Cw:=max C 12
  let cs:=min (1/2) (c/(2*Cw))
  let a:=1+η/2
  have hCw : 0 < Cw:=hC.trans_le (le_max_left _ _)
  have hcs : 0 < cs:=lt_min (by norm_num) (by dsimp only [Cw]; positivity)
  filter_upwards [hbook η hη,
    eventually_reciprocal_ordered (i+1) η Cw a (4*C0) cs hη hCw (by positivity) hcs,
    eventually_reciprocal_windows η c C hη hηu hc hC,
    eventually_reciprocal_message_cost i η c Cw H hη hc hCw hH,
    eventually_ge_atTop (1:ℝ)] with σ hbk hout hwin hcost hσ
  intro q _ hq he V _ _ _ _ _ _ hdim Ω Θ _ _ m p θ F S D J M budget R integer r
    had hmlo hmhi hJ hM hMup hSJ hS hf hcon hclass hsize hbudget hbud hocc
  have hσ0 : 0 < σ:=by linarith
  have hq0 : 0 < (q:ℝ):=he ▸ exp_pos _
  have hqlog : log (Nat.card (ZMod q):ℝ)=σ:=by rw [Nat.card_zmod,←he,log_exp]
  have hD : 1 ≤ D:=(one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
  have hD0 : 0 < D:=by linarith
  obtain ⟨hb,hP,hbP,hτ,hτsmall,⟨book⟩⟩:=hbk q hq he V hdim D R had
  let x:=if integer then (q:ℝ)*σ^(1+η/2) else (q:ℝ)*D*σ^(η/2)
  let n:=⌈x⌉₊
  let k:=⌊(q:ℝ)*D*σ^(3000*beta η)⌋₊
  let L:=4*(n+k)
  let w:=m/L
  have hwindows:=hwin (q:ℝ) D m integer he had.D_lower had.D_upper hmlo hmhi
  change 2 ≤ n ∧ 0 < k ∧ k ≤ n ∧ 1 ≤ w ∧ w*L ≤ m ∧ (m:ℝ)/2 ≤ (w*L:ℕ) ∧
    (1/2)*(q:ℝ)*D*σ^(3000*beta η) ≤ k ∧
    (w:ℝ)*D ≤ Cw*σ^a ∧ (w:ℝ) ≤ Cw*σ^a ∧
    (if integer then (q:ℝ)*σ^(1+η/2) ≤ (n:ℝ) else (c/(2*Cw))*σ^(1+η/2) ≤ (w:ℝ)*D) ∧
    (L:ℝ) ≤ 12*(q:ℝ)*σ^a at hwindows
  obtain ⟨hn,hk,hkn,hw,hwm,hhalf,hklow,hwD,hwup,hcase,hLup⟩:=hwindows
  let T : Θ→Finset (Fin m):=fun _=>prefixSet hwm
  let e:=chosenOrder T hwm
  let G:=orderedTuple T hwm θ F
  let S':=fun z j=>S z (e z j)
  have hGS : ∀ z j,log (S' z j).card ≤ J:=fun z j=>hSJ z (e z j)
  have hG : ∀ x,p.mass x≠0→∀ j,G x j∈S' (θ x) j:=fun x hx j=>hS x hx (e (θ x) j)
  have hgf : ∀ x,p.mass x≠0→∀ j,Incidence.Incident (G x j).1 (G x j).2:=
    fun x hx j=>hf x hx (e (θ x) j)
  have hgcon : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan):=
    fun x hx=>scanConsistent_ordered (F x) (hcon x hx) (e (θ x))
  have hgclass : ∀ x,p.mass x≠0→∀ j,ValidSlotClass (i+3) (scaleKstar σ η D) (S' (θ x) j)
      (.inl (integer,r)):=fun x hx j=>hclass x hx (e (θ x) j)
  have hgsize : ∀ z j,((S' z j).card:ℝ) ≤ 64*(Nat.card (ZMod q):ℝ)^((i+1)+2):=by
    intro z j
    simpa only [Nat.card_zmod] using hsize z (e z j)
  have hgbud : (∑ z,(p.map θ).mass z*((w*(4*(n+k)):ℕ)*J-
      entropy ((p.cond θ z).map G))) ≤ budget :=
    (prefix_budget hwm p θ F S J hS hSJ).trans hbudget
  have hbb : budget ≤ (4*C0)*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) := by
    have hm : (m:ℝ) ≤ 4*(w*(2*(n+k)):ℕ):=by
      push_cast at hhalf ⊢
      dsimp only [L] at hhalf
      push_cast at hhalf
      linarith
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hC0.le)
      (mul_nonneg hD0.le (rpow_nonneg hσ0.le (-beta η)))
    push_cast at hh ⊢
    nlinarith only [hbud,hh]
  have hkc : cs*(Nat.card (ZMod q):ℝ)*D*σ^(3000*beta η) ≤ k := by
    rw [Nat.card_zmod]
    apply le_trans _ hklow
    dsimp only [cs]
    gcongr
    exact min_le_left _ _
  have hnewcase : if integer then
      M ≤ (4*C0)*σ ∧ cs*(Nat.card (ZMod q):ℝ)*σ^(1+η/2) ≤ n ∧
      ∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) V,
        ((univ.filter (fun j : Slot w (n+k)=>covectorTuple (G x) (finProdFinEquiv j)∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M
      else cs*σ^(1+η/2) ≤ (w:ℝ)*D := by
    cases integer
    · simp only [Bool.false_eq_true,ite_false] at hcase ⊢
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (rpow_nonneg hσ0.le _)).trans hcase
    · simp only [ite_true] at hcase ⊢
      refine ⟨by nlinarith,?_,?_⟩
      · rw [Nat.card_zmod]
        have hc1 : cs ≤ 1:=(min_le_left _ _).trans (by norm_num)
        calc
          _  ≤  (q:ℝ)*σ^(1+η/2) := by
            calc
              _ = cs*((q:ℝ)*σ^(1+η/2)) := by ring
              _ ≤ 1*((q:ℝ)*σ^(1+η/2)) := mul_le_mul_of_nonneg_right hc1 (by positivity)
              _ = _ := one_mul _
          _  ≤  _:=hcase
      · intro z hz W
        let ee : Slot w (n+k)↪Fin m:=finProdFinEquiv.toEmbedding.trans (e (θ z)).toEmbedding
        have hh:=count_injective_restriction ee (fun j=>covectorTuple (F z) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)
        apply le_trans _ (hocc z hz W)
        have heq : ∀ j,covectorTuple (G z) (finProdFinEquiv j)=covectorTuple (F z) (ee j) := fun _=>rfl
        simp_rw [heq]
        convert (Nat.cast_le (α:=ℝ)).mpr hh using 1 <;> congr!
  have hne : Nonempty (Fin w):=⟨⟨0,by omega⟩⟩
  obtain ⟨out⟩:=hout (ZMod q) V hdim hqlog D (scaleP σ η D R) H had.D_lower had.D_upper
    book hb hH hP hbP hτ hτsmall Ω Θ w n k p θ G S' integer r J M budget hn hk hkn hwup
      hJ hM hGS hG hgf hgcon hgclass hgsize hgbud hbb hkc hnewcase hne
  have hfinalcost:=hcost q he V hdim D R w n k m had hw hmlo hwD hwup
    (hLup.trans (by dsimp only [Cw];gcongr;exact le_max_right _ _)) hP hbP
  have out' := out.mono (le_refl _) hfinalcost (le_refl 2)
  have final:=out'.transport (Equiv.refl _) F (fun z=>e (θ z)) (fun _ _=>rfl)
  refine ⟨w,w*(n+k),hw,hwD,?_,?_⟩
  · dsimp only [L] at hhalf
    push_cast at hhalf ⊢
    linarith
  · simpa only [Nat.card_zmod] using Nonempty.intro final
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.stepProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.stepDualProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.stepDoubleProjective
theorem eventually_class_step_oai (i : ℕ) (η c C C0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C) (hC0 : 0 < C0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ] (m : ℕ) (p : Law Ω) (θ : Ω→Θ)
      (F : Ω→Fin m→ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q))
      (S : Θ→Fin m→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q)))
      (D J M budget : ℝ) (R : ℕ) (cl : SlotClass (i+3)),
      Admissible σ η D R → c*(q:ℝ)*σ^(1+η) ≤ m → (m:ℝ) ≤ C*q*σ^(1+η) →
      ((i+3:ℕ):ℝ)*σ ≤ J → 0 ≤ M → M ≤ C0*σ →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (θ x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ j,ValidSlotClass (i+3) (scaleKstar σ η D) (S (θ x) j) cl) →
      (∀ z j,((S z j).card:ℝ) ≤ 64*(q:ℝ)^(i+3)) →
      (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map F))) ≤ budget →
      budget ≤ C0*(m:ℝ)*D*σ^(-beta η) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin m=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M) →
      ∃ m' : ℕ, (m:ℝ)/64 ≤ m' ∧
        Nonempty (ContextOutput p F m' (stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(m:ℝ)) 4) := by
  filter_upwards [eventually_reciprocal_step i η c C C0 hη hηu hc hC hC0,
    eventually_high_step η c C0 hη hc hC0 (i+3) (by omega)] with σ hrec hhigh
  intro q _ hq he Ω Θ _ _ m p θ F S D J M budget R cl had hmlo hmhi hJ hM hMup
    hSJ hS hf hcon hclass hsize hbudget hbud hocc
  cases cl with
  | inl cl =>
    obtain ⟨w,m',_,_,hm,⟨e⟩⟩:=hrec q hq he (Fin (i+4)→ZMod q)
      (by simp) Ω Θ m p θ F S D J M budget R cl.1 cl.2 had hmlo hmhi hJ hM hMup
      hSJ hS hf hcon hclass hsize hbudget hbud hocc
    refine ⟨m',by linarith [show (0:ℝ) ≤ m by positivity],⟨e.mono ?_ (le_refl _) (by norm_num)⟩⟩
    gcongr
    exact le_max_left _ _
  | inr cl =>
    obtain ⟨m',hm,⟨e⟩⟩:=hhigh q he Ω Θ m p θ F S D J budget R cl.1 cl.2 had hmlo
      hJ hSJ hS hf hcon hclass hsize hbudget hbud
    refine ⟨m',hm,⟨e.mono ?_ (le_refl _) (le_refl _)⟩⟩
    gcongr
    exact le_max_right _ _
end
end SharpLogRamsey.Marking

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Marking.eventually_class_step_oai := @OAI.SharpLogRamsey.Marking.eventually_class_step_oai
