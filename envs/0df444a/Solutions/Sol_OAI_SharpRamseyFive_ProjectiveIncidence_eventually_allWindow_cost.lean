-- Prove2me | solution 1 for OAI.SharpRamseyFive.ProjectiveIncidence.eventually_allWindow_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:29:38.709709+00:00
-- url     : https://prove2.me/submissions/12f81228-d252-4602-922c-3ba135aeed8c

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_eventually_oriented_guarded_node_cost

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

lemma finite_bounds {η σ D R : ℝ} (hη : 0 < η) (_hη' : η < 1/10)
    (hσ : 1 ≤ σ) (h : Range η σ D R) :
    0 < D ∧ 0 < R ∧ 1 ≤ σ ^ beta η ∧
    σ ^ (9 * beta η) ≤ L η σ D ∧ L η σ D ≤ σ ∧
    σ ^ (10 * beta η) ≤ P η σ D R ∧
    P η σ D R ≤ 4 * σ ^ (1 - η/2 + 9 * beta η) := by
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hb : 0 < beta η := beta_pos hη
  have hx : 1 ≤ σ ^ beta η := Real.one_le_rpow hσ hb.le
  have hd : 0 < D := (Real.rpow_pos_of_pos hs _).trans_le h.dlo
  have hr : 0 < R := (Real.rpow_pos_of_pos hs _).trans_le h.rlo
  have hlo : σ ^ (9 * beta η) ≤ L η σ D := by
    dsimp [L]
    calc
      _ = σ ^ beta η * σ ^ (8 * beta η) := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.dlo (Real.rpow_nonneg hs.le _)
  have hhi : L η σ D ≤ σ := by
    dsimp [L]
    calc
      _ ≤ σ ^ (1-η/2) * σ ^ (8*beta η) := mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)
      _ = σ ^ (1-η/2+8*beta η) := (Real.rpow_add hs _ _).symm
      _ ≤ σ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hσ (by dsimp [beta]; linarith)
      _ = σ := Real.rpow_one _
  refine ⟨hd,hr,hx,hlo,hhi,?_,?_⟩
  · calc
      _ = σ ^ (9*beta η) * σ ^ beta η := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ L η σ D * R := mul_le_mul hlo h.rlo (Real.rpow_nonneg hs.le _) (by dsimp [L]; positivity)
  · have hR : R ≤ 4 * σ ^ beta η := h.rhi.trans (by linarith)
    calc
      _ ≤ (σ ^ (1-η/2) * σ ^ (8*beta η)) * (4*σ ^ beta η) := by
        dsimp [P,L]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)) hR hr.le (by positivity)
      _ = 4 * σ ^ (1-η/2+9*beta η) := by
        rw [show σ ^ (1-η/2) * σ ^ (8*beta η) * (4*σ ^ beta η) =
          4 * ((σ ^ (1-η/2) * σ ^ (8*beta η)) * σ ^ beta η) by ring,
          ← Real.rpow_add hs, ← Real.rpow_add hs]
        congr 2
        ring

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CapDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

lemma cap_subset (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    cap R U q row⊆U := Finset.filter_subset _ _

end SharpRamseyFive.ReverseCap

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AmbientPublicTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma cap_inter (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    U∩cap R Finset.univ q row=cap R U q row := by
  ext a
  simp [cap]

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FreshPublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*}
lemma acceptedIndex_decode {n : ℕ} (E : Finset A) (t : Fin n→A) :
    Option.map t (acceptedIndex E t)=firstAccepted E t :=
  Classical.choose_spec (exists_accepted_index E t)
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma freshEncoded_decoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q) :
    Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t)=
      Option.map (cap R Finset.univ q)
        (firstAccepted (validationRows R S U C n q M)
          (t ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩)) := by
  unfold freshEncoded freshDecoded
  rw [←acceptedIndex_decode]
  simp only [Option.map_map]
  rfl

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseSmallLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma incidences_bidual (S : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) :
    incidences T (S.map bidualPoint.toEmbedding)=incidences S T := by
  have hh : (incidences T (S.map bidualPoint.toEmbedding):ℝ)=(incidences S T:ℝ) := by
    rw [incidences_eq_sum,incidences_eq_sum,Finset.sum_comm]
    simp only [Finset.sum_map,Equiv.toEmbedding_apply,incidenceEntry,incident_bidual]
  exact_mod_cast hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AmbientPairPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_prefixes (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q)
    (m : AmbientPairMessage UB W H q t)
    (hm : ambientPairEncoded A UA B UB W H nA nB q MA MB t=some m) :
    universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1=some m.1 ∧
    let Y := universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m.1
    ValidCap B UB MB (UB∩Y) ∧
    universalFreshEncoded Incident A UA (B∩(UB∩Y)) (UB∩Y) Finset.inter_subset_right H nA q MA t.2=some m.2 := by
  unfold ambientPairEncoded at hm
  cases hf : universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1 with
  | none => simp [hf] at hm
  | some f =>
    rw [hf] at hm
    change (if _hv : ValidCap B UB MB _ then _ else none)=some m at hm
    split_ifs at hm with hv
    obtain ⟨g,hg,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hv,hg⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FourFinitePredictor
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_prefixes (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q)
    (m : FiniteNodeMessage pred UB H q t)
    (hm : finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t=some m) :
    pred.encoded A B t.1=some m.1 ∧ CaptureBound A UA c M (pred.decoded t.1 m.1) ∧
    ambientPairEncoded A UA B UB (pred.decoded t.1 m.1) H nA nB q MA MB t.2=some m.2 := by
  unfold finiteNodeEncoded at hm
  cases hf : pred.encoded A B t.1 with
  | none => simp [hf] at hm
  | some f =>
    rw [hf] at hm
    change (if _hc : CaptureBound A UA c M _ then _ else none)=some m at hm
    split_ifs at hm with hc
    obtain ⟨g,hg,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hc,hg⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_FiniteNodeSent
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]
lemma freshEncoded_valid (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q)
    (m : FreshMessage W n q) (hm : freshEncoded R S U C W hCW n q M t=some m) :
    ValidCap S U M (U∩freshDecoded R W n q t m) := by
  have hh := freshEncoded_decoded R S U C W hCW n q M t
  rw [hm,Option.map_some] at hh
  obtain ⟨row,hr,he⟩ := Option.map_eq_some_iff.mp hh.symm
  have hi := (firstAccepted_index _ _ hr).choose_spec.2
  rw [←he,cap_inter]
  exact ⟨cap_subset _ _ _ _,(Finset.mem_filter.mp hi).2.2⟩

lemma universalFreshEncoded_valid (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q)
    (hm : universalFreshEncoded R S U C W hCW H n q M t=some m) :
    ValidCap S U M (U∩universalFreshDecoded R W H q t m) := by
  unfold universalFreshEncoded at hm
  split_ifs at hm with hW
  obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
  subst m
  simp only [universalFreshDecoded,dite_eq_left hW]
  exact freshEncoded_valid R S U C W hCW n q M _ f hf
end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_sent_valid (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ)
    (t : FiniteNodeTape pred H q) (m : FiniteNodeMessage pred UB H q t)
    (hm : finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t=some m) :
    ValidCap B UB MB (UB∩(finiteNodeDecoded pred UB H q t m).1) ∧
    ValidCap A UA MA (UA∩(finiteNodeDecoded pred UB H q t m).2) := by
  have hp := (finiteNode_prefixes pred A UA B UB H nA nB q MA MB c M t m hm).2.2
  have hh := ambientPair_prefixes A UA B UB (pred.decoded t.1 m.1) H nA nB q MA MB t.2 m.2 hp
  exact ⟨hh.2.1,universalFreshEncoded_valid _ _ _ _ _ _ _ _ _ _ _ _ hh.2.2⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeSent
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma guardedNode_sent_valid (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K))
    (m : FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t=some m) :
    OriginalNodeReady A₀ UA B₀ UB δ τ ∧
    ValidCap (B₀∩UB) UB ((320/c+320)*(Nat.card K:ℝ)^5/(A₀∩UA).card)
      (UB∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).1) ∧
    ValidCap (A₀∩UA) UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/(B₀∩UB).card)
      (UA∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).2) := by
  unfold guardedNodeEncoded at hm
  split_ifs at hm with hr
  exact ⟨hr,finiteNode_sent_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm⟩

lemma guardedNode_original_capture (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K))
    (m : FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t=some m) :
    (9/10:ℝ)*δ*A₀.card≤(A₀∩(UA∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)).card ∧
    (9/10:ℝ)*δ*B₀.card≤(B₀∩(UB∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).1)).card := by
  obtain ⟨hr,hB,hA⟩ := guardedNode_sent_valid pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t m hm
  have ha := hA.2.2
  have hb := hB.2.2
  simp only [Finset.inter_assoc,Finset.inter_left_idem] at ha hb
  constructor
  · nlinarith [hr.1]
  · nlinarith [hr.2.1]
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ReadyRefinement
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_trimmed_product (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (τ b : ℝ) (hr : OriginalNodeReady A₀ UA B₀ UB (9/10) τ)
    (hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card) :
    (Nat.card K:ℝ)^5*Real.exp (-(b+1))≤((A₀∩UA).card:ℝ)*(B₀∩UB).card := by
  have hmul := mul_le_mul hr.1 hr.2.1
    (show (0:ℝ)≤(9/10:ℝ)*B₀.card by positivity) (Nat.cast_nonneg (A₀∩UA).card)
  have he : Real.exp (-1)≤(81:ℝ)/100 := by
    rw [Real.exp_neg]
    rw [←one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := Real.add_one_le_exp (1:ℝ)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left he
    (show (0:ℝ)≤(Nat.card K:ℝ)^5*Real.exp (-b) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤81/100)
  rw [neg_add,Real.exp_add]
  nlinarith only [hmul,h1,h2]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_bidual (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V))) (δ τ : ℝ) :
    OriginalNodeReady B₀ UB (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) δ τ ↔
      OriginalNodeReady A₀ UA B₀ UB δ τ := by
  simp only [OriginalNodeReady,←Finset.map_inter,Finset.card_map,incidences_bidual]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨h2,h1,?_⟩ <;> nlinarith only [h3]

end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
    [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma bidual_inter_card (A UA : Finset (ℙ K V)) (Y : Finset (ℙ K (Dual K (Dual K V)))) :
    (A.map bidualPoint.toEmbedding∩(UA.map bidualPoint.toEmbedding∩Y)).card=
      (A∩(UA∩Y.map bidualPoint.symm.toEmbedding)).card := by
  have he : A.map bidualPoint.toEmbedding∩(UA.map bidualPoint.toEmbedding∩Y)=
      (A∩(UA∩Y.map bidualPoint.symm.toEmbedding)).map bidualPoint.toEmbedding := by
    ext x
    simp
  rw [he,Finset.card_map]

theorem orientedGuardedNode_original_capture
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t=some m) :
    OriginalNodeReady A₀ UA B₀ UB δ τ ∧
    (9/10:ℝ)*δ*A₀.card≤
      (A₀∩(UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)).card ∧
    (9/10:ℝ)*δ*B₀.card≤
      (B₀∩(UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1)).card := by
  unfold orientedGuardedNodeEncoded at hm
  split_ifs at hm with hAB
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    have hv := (guardedNode_sent_valid f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm').1
    exact ⟨hv,guardedNode_original_capture f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm'⟩
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    have hv := (guardedNode_sent_valid r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm').1
    have hh := guardedNode_original_capture r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm'
    refine ⟨(ready_bidual A₀ UA B₀ UB δ τ).mp hv,?_,hh.1⟩
    simpa only [Finset.card_map,bidual_inter_card,orientedNodeDecoded,reverseNodePair] using hh.2

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_PivotPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree

lemma cap_potential (u c n Q C : ℝ) (hn : 0<n) (hu : n≤u)
    (hc : 0 < c) (hQ : 0<Q) (hC : 1≤C) (hcap : c≤C*Q/n) :
    potential c u Q ≤ Real.log (u/n)+Real.log C := by
  have hu0 : 0<u := hn.trans_le hu
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hd : 0≤Real.log (u/n) := Real.log_nonneg ((le_div_iff₀ hn).mpr (by simpa using hu))
  have hlC : 0≤Real.log C := Real.log_nonneg hC
  have hratio : c*u/Q≤C*(u/n) := by
    have hh := mul_le_mul_of_nonneg_right hcap hu0.le
    apply (div_le_iff₀ hQ).mpr
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have hlog := Real.log_le_log (div_pos (mul_pos hc hu0) hQ) hratio
  rw [Real.log_mul hC0.ne' (div_pos hu0 hn).ne'] at hlog
  exact max_le (add_nonneg hd hlC) (by linarith)

theorem split_potential (uA uB nA nB cA cB Q C : ℝ)
    (hnA : 0<nA) (hnB : 0<nB) (hAu : nA≤uA) (hBu : nB≤uB)
    (hcA : 0 < cA) (hcB : 0 < cB) (hQ : 0<Q) (hC : 1≤C)
    (hAcap : cA≤C*Q/nB) (hBcap : cB≤C*Q/nA) :
    potential cA uB Q+potential uA cB Q ≤
      potential uA uB Q+Real.log (Q/(nA*nB))+2*Real.log C := by
  have h₁ := cap_potential uB cA nB Q C hnB hBu hcA hQ hC hAcap
  have h₂ := cap_potential uA cB nA Q C hnA hAu hcB hQ hC hBcap
  rw [potential,mul_comm cB uA] at h₂
  have huA : uA≠0 := (hnA.trans_le hAu).ne'
  have huB : uB≠0 := (hnB.trans_le hBu).ne'
  have hid : Real.log (uA/nA)+Real.log (uB/nB)=
      Real.log (uA*uB/Q)+Real.log (Q/(nA*nB)) := by
    rw [Real.log_div huA hnA.ne',Real.log_div huB hnB.ne',
      Real.log_div (mul_ne_zero huA huB) hQ.ne',
      Real.log_div hQ.ne' (mul_ne_zero hnA.ne' hnB.ne'),
      Real.log_mul huA huB,Real.log_mul hnA.ne' hnB.ne']
    ring
  have hG : Real.log (uA*uB/Q)≤potential uA uB Q := le_max_right _ _
  change potential cA uB Q+max 0 (Real.log (uA*cB/Q))≤_
  linarith

lemma log_deficits (uA uB nA nB Q : ℝ) (hnA : 0<nA) (hnB : 0<nB)
    (hAu : nA≤uA) (hBu : nB≤uB) (hQ : 0<Q) :
    Real.log (uA/nA)+Real.log (uB/nB) ≤
      potential uA uB Q+Real.log (Q/(nA*nB)) := by
  have huA : uA≠0 := (hnA.trans_le hAu).ne'
  have huB : uB≠0 := (hnB.trans_le hBu).ne'
  have he : Real.log (uA/nA)+Real.log (uB/nB)=
      Real.log (uA*uB/Q)+Real.log (Q/(nA*nB)) := by
    rw [Real.log_div huA hnA.ne',Real.log_div huB hnB.ne',
      Real.log_div (mul_ne_zero huA huB) hQ.ne',
      Real.log_div hQ.ne' (mul_ne_zero hnA.ne' hnB.ne'),
      Real.log_mul huA huB,Real.log_mul hnA.ne' hnB.ne']
    ring
  rw [he]
  have hh : Real.log (uA*uB/Q)≤potential uA uB Q := le_max_right _ _
  linarith

lemma initial_potential (q uA uB : ℝ) (hq : 1≤q) (hA : 0<uA) (hB : 0<uB)
    (hAu : uA≤2*q^4) (hBu : uB≤2*q^4) :
    potential uA uB (q^5)≤3*Real.log q+Real.log 4 := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hprod := mul_le_mul hAu hBu hB.le (by positivity : (0:ℝ)≤2*q^4)
  have hratio : uA*uB/q^5 ≤ 4*q^3 := by
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    nlinarith only [hprod]
  have hl := Real.log_le_log (by positivity : 0<uA*uB/q^5) hratio
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (pow_ne_zero _ hq0.ne'),Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  exact max_le (by positivity [Real.log_nonneg hq,Real.log_nonneg (by norm_num : (1:ℝ)≤4)])
    (by linarith)

end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GuardedNodeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_log_deficits (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (τ b : ℝ)
    (hr : OriginalNodeReady A₀ UA B₀ UB (9/10) τ)
    (hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card) :
    Real.log ((UA.card:ℝ)/(A₀∩UA).card)+Real.log ((UB.card:ℝ)/(B₀∩UB).card)≤
      potential UA.card UB.card ((Nat.card K:ℝ)^5)+(b+1) := by
  have hnA := nonempty_of_positive_trim _ _ hA₀ (9/10) (by norm_num) hr.1
  have hnB := nonempty_of_positive_trim _ _ hB₀ (9/10) (by norm_num) hr.2.1
  have hnA' : (0:ℝ)<(A₀∩UA).card := by exact_mod_cast hnA.card_pos
  have hnB' : (0:ℝ)<(B₀∩UB).card := by exact_mod_cast hnB.card_pos
  have hQ : (0:ℝ)<(Nat.card K:ℝ)^5 := by
    have hh : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos
    exact pow_pos hh _
  have hd := log_deficits UA.card UB.card (A₀∩UA).card (B₀∩UB).card ((Nat.card K:ℝ)^5)
    hnA' hnB' (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=A₀) (s₂:=UA)))
    (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=B₀) (s₂:=UB))) hQ
  have ht := ready_trimmed_product A₀ UA B₀ UB τ b hr hp
  have he : Real.exp (-(b+1))*Real.exp (b+1)=1 := by rw [←Real.exp_add];simp
  have hx : (Nat.card K:ℝ)^5≤((A₀∩UA).card:ℝ)*(B₀∩UB).card*Real.exp (b+1) := by
    calc
      _=(((Nat.card K:ℝ)^5)*Real.exp (-(b+1)))*Real.exp (b+1) := by rw [mul_assoc,he,mul_one]
      _≤_ := mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
  have hlog : Real.log (((Nat.card K:ℝ)^5)/(((A₀∩UA).card:ℝ)*(B₀∩UB).card))≤b+1 := by
    apply (Real.log_le_iff_le_exp (div_pos hQ (mul_pos hnA' hnB'))).mpr
    apply (div_le_iff₀ (mul_pos hnA' hnB')).mpr
    simpa only [mul_comm (Real.exp (b+1))] using hx
  linarith only [hd,hlog]

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_PivotTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open BinaryTree

lemma balanced_height (H lo n : ℕ) (hn : n<2^H) :
    (balanced lo n).height≤H := by
  induction H generalizing lo n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simp [balanced]
  | succ H ih =>
    cases n with
    | zero => simp [balanced]
    | succ n =>
      rw [pow_succ] at hn
      have hl : n/2<2^H := by omega
      have hr : n-n/2<2^H := by omega
      simp only [balanced,BinaryTree.height]
      exact Nat.succ_le_succ (max_le (ih lo (n/2) hl) (ih _ _ hr))

end SharpRamseyFive.PivotTree

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)

variable (left right : ∀a c t,M a c t→C)

omit [Fintype C] in
lemma retained_nodes_le (b : BinaryTree A) (ω : Tape Ω b) (c : C)
    (m : Message Ω M left right b ω c) :
    (retained Ω M left right b ω c m).numNodes≤b.numNodes := by
  induction b generalizing c with
  | nil => simp only [retained,BinaryTree.numNodes,le_refl]
  | node a l r hl hr =>
    cases m with
    | none => exact Nat.zero_le _
    | some m =>
      exact Nat.add_le_add (Nat.add_le_add (hl _ _ m.2.1) (hr _ _ m.2.2)) le_rfl

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_TreeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)
  (left right : ∀a c t,M a c t→C)

omit [Fintype C] in
lemma slotCost_le (lc : ∀a c t,M a c t→ℝ)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) (m : Message Ω M left right b ω c) :
    slotCost Ω M left right lc b ω c m ≤ cost Ω M left right lc b ω c m+
      (2*((retained Ω M left right b ω c m).numNodes:ℝ)+1)*Real.log 2 := by
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  induction b generalizing c with
  | nil => simp [slotCost,cost,retained,BinaryTree.numNodes,hlog]
  | node a l r hl hr =>
    cases m with
    | none => simp [slotCost,cost,retained,BinaryTree.numNodes]
    | some m =>
      have h1 := hl ω.2.1 _ m.2.1
      have h2 := hr ω.2.2 _ m.2.2
      simp only [slotCost,cost,retained,BinaryTree.numNodes,Nat.cast_add,Nat.cast_one]
      linarith only [h1,h2]
end SharpRamseyFive.TreeCodec
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MessageCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)
  (left right : ∀a c t,M a c t→C)
omit [Fintype C] in
lemma slotCost_le_original (lc : ∀a c t,M a c t→ℝ)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) (m : Message Ω M left right b ω c) :
    slotCost Ω M left right lc b ω c m ≤ cost Ω M left right lc b ω c m+
      (2*(b.numNodes:ℝ)+1)*Real.log 2 := by
  have hn : ((retained Ω M left right b ω c m).numNodes:ℝ)≤b.numNodes := by
    exact_mod_cast retained_nodes_le Ω M left right b ω c m
  have hh := mul_le_mul_of_nonneg_right (show 2*((retained Ω M left right b ω c m).numNodes:ℝ)+1≤2*(b.numNodes:ℝ)+1 by linarith)
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  have hl := slotCost_le Ω M left right lc b ω c m
  linarith only [hl,hh]
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedNodeCaps
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma bidual_cap_card (UA : Finset (ℙ K V)) (Y : Finset (ℙ K (Dual K (Dual K V)))) :
    (UA.map bidualPoint.toEmbedding∩Y).card=(UA∩Y.map bidualPoint.symm.toEmbedding).card := by
  simpa only [Finset.inter_assoc,Finset.inter_left_idem] using bidual_inter_card UA UA Y

theorem orientedGuardedNode_caps
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t=some m) :
    ((UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2).card:ℝ)≤
      (320/c+320)*((Nat.card K:ℝ)^5)/(B₀∩UB).card ∧
    ((UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1).card:ℝ)≤
      (320/c+320)*((Nat.card K:ℝ)^5)/(A₀∩UA).card := by
  have hC : (320/((9:ℝ)/10)+320)≤320/c+320 := by
    have hh : (320:ℝ)/((9:ℝ)/10)≤320/c := div_le_div_of_nonneg_left (by norm_num) hc hc9
    linarith only [hh]
  have hM (n : ℕ) : (320/((9:ℝ)/10)+320)*((Nat.card K:ℝ)^5)/n≤
      (320/c+320)*((Nat.card K:ℝ)^5)/n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (Nat.cast_nonneg n)
  unfold orientedGuardedNodeEncoded at hm
  split_ifs at hm with hAB
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨_,hB,hA⟩ := guardedNode_sent_valid f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm'
    exact ⟨hA.2.1.trans (hM _),hB.2.1⟩
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨_,hA,hB⟩ := guardedNode_sent_valid r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm'
    constructor
    · simpa only [orientedNodeDecoded,reverseNodePair,bidual_cap_card] using hA.2.1
    · have hh := hB.2.1
      simp only [←Finset.map_inter,Finset.card_map] at hh
      exact hh.trans (hM _)

theorem orientedGuardedNode_split_potential
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c τ P b : ℝ) (hc : 0 < c) (hc9 : c≤9/10)
    (hp : ((Nat.card K:ℝ)^5)*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c (9/10) τ P (by norm_num) t=some m) :
    potential (UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2).card
        UB.card ((Nat.card K:ℝ)^5)+
      potential UA.card (UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1).card
        ((Nat.card K:ℝ)^5)≤
      potential UA.card UB.card ((Nat.card K:ℝ)^5)+(b+1)+2*Real.log (320/c+320) := by
  obtain ⟨hready,hca,hcb⟩ := orientedGuardedNode_original_capture f r σ hσ hq hd A₀ UA B₀ UB
    hA₀ hB₀ c (9/10) τ P (by norm_num) t m hm
  obtain ⟨hAcap,hBcap⟩ := orientedGuardedNode_caps f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀
    c (9/10) τ P hc hc9 (by norm_num) t m hm
  have hnA := nonempty_of_positive_trim _ _ hA₀ (9/10) (by norm_num) hready.1
  have hnB := nonempty_of_positive_trim _ _ hB₀ (9/10) (by norm_num) hready.2.1
  have hcA := (nonempty_of_positive_trim _ _ hA₀ ((9/10)*(9/10)) (by norm_num) hca).mono Finset.inter_subset_right
  have hcB := (nonempty_of_positive_trim _ _ hB₀ ((9/10)*(9/10)) (by norm_num) hcb).mono Finset.inter_subset_right
  have hQ : (0:ℝ)<((Nat.card K:ℝ)^5) := by rw [←hq];positivity
  have hnA' : (0:ℝ)<(A₀∩UA).card := by exact_mod_cast hnA.card_pos
  have hnB' : (0:ℝ)<(B₀∩UB).card := by exact_mod_cast hnB.card_pos
  have hsplit := split_potential UA.card UB.card (A₀∩UA).card (B₀∩UB).card _ _ ((Nat.card K:ℝ)^5) (320/c+320)
    hnA' hnB' (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=A₀) (s₂:=UA)))
    (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=B₀) (s₂:=UB)))
    (by exact_mod_cast hcA.card_pos) (by exact_mod_cast hcB.card_pos) hQ
    (by
      have hh : 0≤(320:ℝ)/c := by positivity
      linarith only [hh]) hAcap hBcap
  have ht := ready_trimmed_product A₀ UA B₀ UB τ b hready hp
  have he : Real.exp (-(b+1))*Real.exp (b+1)=1 := by rw [←Real.exp_add];simp
  have hx : ((Nat.card K:ℝ)^5)≤((A₀∩UA).card:ℝ)*(B₀∩UB).card*Real.exp (b+1) := by
    calc
      _=(((Nat.card K:ℝ)^5)*Real.exp (-(b+1)))*Real.exp (b+1) := by rw [mul_assoc,he,mul_one]
      _≤_ := mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
  have hb : Real.log (((Nat.card K:ℝ)^5)/(((A₀∩UA).card:ℝ)*(B₀∩UB).card))≤b+1 := by
    apply (Real.log_le_iff_le_exp (div_pos hQ (mul_pos hnA' hnB'))).mpr
    apply (div_le_iff₀ (mul_pos hnA' hnB')).mpr
    simpa only [mul_comm (Real.exp (b+1))] using hx
  linarith only [hsplit,hb]
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_EncodedTreePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)
  (left right : ∀a c t,M a c t→C)
  (enc : ∀a c t,Option (M a c t))

omit [Fintype C] in
theorem encoded_potential_le (φ : C→ℝ) (B : ℝ) (hφ : ∀c,0≤φ c) (hB : 0≤B)
    (hsplit : ∀a c t m,enc a c t=some m→φ (left a c t m)+φ (right a c t m)≤φ c+B)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) :
    cost Ω M left right (fun _ c _ _=>φ c) b ω c (encoded Ω M left right enc b ω c)≤
      b.height*(φ c+B*b.numNodes) := by
  induction b generalizing c with
  | nil => simp [cost]
  | node a l r ihl ihr =>
    cases he : enc a c (ω.1 c) with
    | none =>
      simp only [encoded,he,Option.map_none,cost]
      exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hφ c) (mul_nonneg hB (Nat.cast_nonneg _)))
    | some m =>
      have hl := ihl ω.2.1 (left a c (ω.1 c) m)
      have hr := ihr ω.2.2 (right a c (ω.1 c) m)
      have hL : (l.height:ℝ)≤ max l.height r.height := by exact_mod_cast le_max_left l.height r.height
      have hR : (r.height:ℝ)≤ max l.height r.height := by exact_mod_cast le_max_right l.height r.height
      have hl' := hl.trans (mul_le_mul_of_nonneg_right hL
        (add_nonneg (hφ _) (mul_nonneg hB (Nat.cast_nonneg l.numNodes))))
      have hr' := hr.trans (mul_le_mul_of_nonneg_right hR
        (add_nonneg (hφ _) (mul_nonneg hB (Nat.cast_nonneg r.numNodes))))
      have hs := mul_le_mul_of_nonneg_left (hsplit a c (ω.1 c) m he) (Nat.cast_nonneg (max l.height r.height))
      simp only [encoded,he,Option.map_some,cost,BinaryTree.height,BinaryTree.numNodes,
        Nat.cast_add,Nat.cast_one]
      nlinarith only [hl',hr',hs,mul_nonneg hB (Nat.cast_nonneg l.numNodes),
        mul_nonneg hB (Nat.cast_nonneg r.numNodes),hB]

omit [Fintype C] in
theorem encoded_cost_linear (φ : C→ℝ) (lc : ∀a c t,M a c t→ℝ)
    (X D : ℝ) (hD : 0≤D)
    (hlc : ∀a c t m,enc a c t=some m→lc a c t m≤X*φ c+D)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) :
    cost Ω M left right lc b ω c (encoded Ω M left right enc b ω c)≤
      X*cost Ω M left right (fun _ c _ _=>φ c) b ω c (encoded Ω M left right enc b ω c)+D*b.numNodes := by
  induction b generalizing c with
  | nil => simp [cost]
  | node a l r ihl ihr =>
    cases he : enc a c (ω.1 c) with
    | none => simp only [encoded,he,Option.map_none,cost,mul_zero,zero_add];positivity
    | some m =>
      have hl := ihl ω.2.1 (left a c (ω.1 c) m)
      have hr := ihr ω.2.2 (right a c (ω.1 c) m)
      have hs := hlc a c (ω.1 c) m he
      simp only [encoded,he,Option.map_some,cost,BinaryTree.numNodes,Nat.cast_add,Nat.cast_one]
      linarith only [hl,hr,hs]

omit [Fintype C] in
theorem encoded_cost_le (φ : C→ℝ) (lc : ∀a c t,M a c t→ℝ)
    (B X D : ℝ) (hφ : ∀c,0≤φ c) (hB : 0≤B) (hX : 0≤X) (hD : 0≤D)
    (hsplit : ∀a c t m,enc a c t=some m→φ (left a c t m)+φ (right a c t m)≤φ c+B)
    (hlc : ∀a c t m,enc a c t=some m→lc a c t m≤X*φ c+D)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) :
    cost Ω M left right lc b ω c (encoded Ω M left right enc b ω c)≤
      X*b.height*(φ c+B*b.numNodes)+D*b.numNodes := by
  have hc := encoded_cost_linear Ω M left right enc φ lc X D hD hlc b ω c
  have hp := mul_le_mul_of_nonneg_left
    (encoded_potential_le Ω M left right enc φ B hφ hB hsplit b ω c) hX
  nlinarith only [hc,hp]
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrientedTreeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

lemma nodeChargeConstant_nonneg : 0≤nodeChargeConstant := by
  have h1 : Real.log ((9:ℝ)/100000)≤0 := Real.log_nonpos (by norm_num) (by norm_num)
  have h2 : Real.log ((9:ℝ)/10)≤0 := Real.log_nonpos (by norm_num) (by norm_num)
  unfold nodeChargeConstant
  linarith only [h1,h2]

theorem eventually_oriented_tree_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (ι : Type)
      (A₀ : ι→Finset (ℙ K V)) (B₀ : ι→Finset (ℙ K (Dual K V)))
      (hA₀ : ∀i,(A₀ i).Nonempty) (hB₀ : ∀i,(B₀ i).Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      (∀i,(Nat.card K:ℝ)^5*Real.exp (-b)≤((A₀ i).card:ℝ)*(B₀ i).card) →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      let X := nodeChargeConstant*(Nat.card K:ℝ)*(P η σ D R)
      ∀ (tree : BinaryTree ι) (ω : OrientedPivotTreeTape f r tree) (C : PivotContext K V),
      TreeCodec.cost (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
        (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
        (fun _ C t m=>orientedNodeCost (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m)
        tree ω C
        (orientedPivotTreeEncoded f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ (9/100000) (9/10)
          (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω C)≤
      X*tree.height*(pivotPotential C+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*tree.numNodes)+
        (Real.log 2+X*(b+1+P η σ D R))*tree.numNodes := by
  filter_upwards [eventually_oriented_guarded_node_cost hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd ι A₀ B₀ hA₀ hB₀ hσ hq hcard hr hL hb hbhi hp
  dsimp only
  intro tree ω C
  have hP : 0≤P η σ D R := by
    obtain ⟨_,_,_,_,_,hP,_⟩ := finite_bounds hη hη' hσ hr
    exact (Real.rpow_nonneg (by linarith : 0≤σ) _).trans hP
  have hX : 0≤nodeChargeConstant*(Nat.card K:ℝ)*(P η σ D R) := by
    exact mul_nonneg (mul_nonneg nodeChargeConstant_nonneg (Nat.cast_nonneg _)) hP
  apply TreeCodec.encoded_cost_le
    (φ:=pivotPotential) (B:=b+1+2*Real.log (320/((9:ℝ)/100000)+320))
  · intro C
    exact le_max_left _ _
  · have hl := Real.log_nonneg (show 1≤320/((9:ℝ)/100000)+320 by norm_num)
    linarith only [hb,hl]
  · exact hX
  · exact add_nonneg (Real.log_nonneg (by norm_num))
      (mul_nonneg hX (by linarith only [hb,hP]))
  · intro i U t m hm
    simpa only [pivotPotential,orientedPivotLeft,orientedPivotRight,add_assoc] using
      orientedGuardedNode_split_potential _ _ σ hσ hq hd.le (A₀ i) U.1 (B₀ i) U.2
        (hA₀ i) (hB₀ i) (9/100000) (σ^(-1000*beta η)) (P η σ D R) b
        (by norm_num) (by norm_num) (hp i) t m hm
  · intro i U t m hm
    have hready := (orientedGuardedNode_original_capture _ _ σ hσ hq hd.le (A₀ i) U.1 (B₀ i) U.2
      (hA₀ i) (hB₀ i) (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R)
      (by norm_num) t m hm).1
    have hc := hn D b R L₀ q K V hd (A₀ i) U.1 (B₀ i) U.2 (hA₀ i) (hB₀ i)
      hσ hq hcard hr hL hb hbhi hready (hp i) t m hm
    have hg := ready_log_deficits (A₀ i) U.1 (B₀ i) U.2 (hA₀ i) (hB₀ i) _ b hready (hp i)
    have hm' := mul_le_mul_of_nonneg_left (add_le_add_right hg (P η σ D R)) hX
    change _≤_ * pivotPotential U+_
    dsimp only [pivotPotential,nodeChargeConstant] at hc hm' ⊢
    nlinarith only [hc,hm']
end

open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology BigOperators

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
variable {I J : Type*} [Preorder I] [Preorder J]

omit [Preorder I] [Preorder J] in
lemma map_height (g : I→J) (b : BinaryTree I) : (b.map g).height=b.height := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>simp only [BinaryTree.map,BinaryTree.height,ihl,ihr]

end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.PivotTree
open BinaryTree TreeCodec

lemma finiteBalanced_height (H n : ℕ) (hn : n<2^H) : (finiteBalanced n).height≤H := by
  rw [finiteBalanced,map_height]
  exact balanced_height H 0 n hn

end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_VariableTreeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section

theorem eventually_variable_tree_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (w : ℕ) (m : Fin (w+1))
      (A₀ : Fin (m.val+1)→Finset (ℙ K V)) (B₀ : Fin (m.val+1)→Finset (ℙ K (Dual K V)))
      (hA₀ : ∀i,(A₀ i).Nonempty) (hB₀ : ∀i,(B₀ i).Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      (∀i,(Nat.card K:ℝ)^5*Real.exp (-b)≤((A₀ i).card:ℝ)*(B₀ i).card) →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      let X := nodeChargeConstant*(Nat.card K:ℝ)*(P η σ D R)
      ∀ (t : VariableTreeTape f r w) (C : PivotContext K V),
      variableTreeCost f r t C
        (variableTreeEncoded f r t C m σ hσ hq hd.le A₀ B₀ hA₀ hB₀
          (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num))≤
      Real.log (w+1)+
      (X*(finiteBalanced m.val).height*
        (pivotPotential C+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*m.val)+
        (Real.log 2+X*(b+1+P η σ D R))*m.val)+
        (2*(m.val:ℝ)+1)*Real.log 2 := by
  filter_upwards [eventually_oriented_tree_cost hη hη' Cb hCb] with σ hh
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd w m A₀ B₀ hA₀ hB₀ hσ hq hcard hr hL hb hbhi hp
  dsimp only
  intro t C
  have h:=hh D b R L₀ q K V hd (Fin (m.val+1)) A₀ B₀ hA₀ hB₀ hσ hq hcard hr hL
    hb hbhi hp (finiteBalanced m.val) (t m) C
  let f := fun U : PivotContext K V=>fourFinitePredictor hd σ U.1 U.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun U : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ U.2 (U.1.map bidualPoint.toEmbedding)
      (P η σ D R) (σ^(-800*beta η)) R L₀
  have hs := TreeCodec.slotCost_le_original
    (fun _ : Fin (m.val+1)=>OrientedPivotTape f r)
    (fun _ : Fin (m.val+1)=>OrientedPivotMessage f r)
    (fun _ : Fin (m.val+1)=>orientedPivotLeft f r)
    (fun _ : Fin (m.val+1)=>orientedPivotRight f r)
    (fun _ U t m=>orientedNodeCost (f U) (r U) U.1 U.2
      (1000*(Nat.card K)^2) (Nat.card K) t m)
    (finiteBalanced m.val) (t m) C
    (orientedPivotTreeEncoded f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀
      (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num)
      (finiteBalanced m.val) (t m) C)
  have hh' := hs.trans (add_le_add h le_rfl)
  simp only [finiteBalanced_nodes] at hh'
  unfold variableTreeCost variableTreeEncoded
  dsimp only
  simpa only [orientedPivotSlotCost, f, r, add_assoc] using add_le_add_right hh' (Real.log (w+1))
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AmbientPivotPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module PivotTree
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma projective_card_pos_of_five (hd : finrank K V=5) :
    0<Fintype.card (ℙ K V) := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V (show finrank K V=4+1 from hd)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero]
  omega

omit [FiniteDimensional K V] in
lemma ambient_pivotPotential (hd : finrank K V=5) (σ : ℝ)
    (hq : Real.exp σ=Nat.card K) :
    pivotPotential (K:=K) (V:=V) (Finset.univ,Finset.univ)≤3*σ+Real.log 4 := by
  have hq2 : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have ha := projective_card_pos_of_five hd
  have hb := projective_card_pos_of_five (K:=K) (V:=Dual K V) (by simpa using hd)
  have hA := projective_card_le_two_pow (d:=4) hd hq2
  have hB := projective_card_le_two_pow (K:=K) (V:=Dual K V) (d:=4) (by simpa using hd) hq2
  have hl : Real.log (Nat.card K:ℝ)=σ := by rw [←hq,Real.log_exp]
  have hh := initial_potential (Nat.card K:ℝ) (Fintype.card (ℙ K V))
    (Fintype.card (ℙ K (Dual K V))) (by exact_mod_cast (show 1≤Nat.card K by omega))
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hA) (by exact_mod_cast hB)
  simpa only [pivotPotential,Finset.card_univ,hl] using hh
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_EmptyVariableTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
omit [Finite K] in
private lemma emptyTreeCost {I : Type} (b : BinaryTree I) (h : b=.nil)
    (t : OrientedPivotTreeTape f r b) (C : PivotContext K V)
    (m : OrientedPivotTreeMessage f r b t C) : orientedPivotSlotCost f r b t C m=0 := by
  subst b
  rfl

omit [Finite K] in
lemma variableTreeEmpty_cost {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V) :
    variableTreeCost f r t C (variableTreeEmpty f r t C)=Real.log (w+1) := by
  unfold variableTreeCost variableTreeEmpty
  dsimp only
  rw [emptyTreeCost f r (finiteBalanced 0) (by simp [finiteBalanced,balanced,BinaryTree.map])]
  exact add_zero _
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLevelProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalLevels.first_size {p : Law (FlagPair K V)} {u s : ℝ}
    (L : ReciprocalLevels p u s) (A : Finset (ℙ K V)) (hA : 0<L.firstLaw A) :
    Real.exp (5*Real.log (Nat.card K)-u-s)/2≤(A.card:ℝ) := by
  have h:=(L.first_good A hA).2.2.1
  have he : Real.exp (5*Real.log (Nat.card K)-u)*Real.exp (-s)=
      Real.exp (5*Real.log (Nat.card K)-u-s) := by rw [←Real.exp_add]; congr 1
  nlinarith [Real.exp_pos (5*Real.log (Nat.card K)-u-s)]
omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalLevels.second_size {p : Law (FlagPair K V)} {u s : ℝ}
    (L : ReciprocalLevels p u s) (B : Finset (ℙ K (Dual K V))) (hB : 0<L.secondLaw B) :
    Real.exp (u-s)/2≤(B.card:ℝ) := by
  have h:=(L.second_good B hB).2.2.1
  have he : Real.exp u*Real.exp (-s)=Real.exp (u-s) := by rw [←Real.exp_add]; congr 1
  nlinarith [Real.exp_pos (u-s)]

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section

theorem pivot_support_product (q u v k d a b : ℝ) (hq : 0<q)
    (hdrop : u-v≤d)
    (ha : Real.exp (5*Real.log q-u-k)/2≤a)
    (hb : Real.exp (v-k)/2≤b) :
    q^5*Real.exp (-d-2*k)/4≤a*b := by
  have he : Real.exp (5*Real.log q-u-k)/2*(Real.exp (v-k)/2)=
      q^5*Real.exp (v-u-2*k)/4 := by
    rw [div_mul_div_comm,←Real.exp_add]
    have hx : (5*Real.log q-u-k)+(v-k)=5*Real.log q+(v-u-2*k) := by ring
    have hfive : Real.exp (5*Real.log q)=Real.exp (Real.log q)^5 := by
      simpa using Real.exp_nat_mul (Real.log q) 5
    rw [hx,Real.exp_add,hfive,Real.exp_log hq]
    norm_num
  have hle := mul_le_mul ha hb (by positivity : 0≤Real.exp (v-k)/2)
    ((by positivity : 0≤Real.exp (5*Real.log q-u-k)/2).trans ha)
  rw [he] at hle
  refine le_trans ?_ hle
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]

namespace ReciprocalWindows
local instance windowLevelsBlockDE_ra79e00_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.windowLevelsIndexDE
variable {p : Law (Slots w r→FlagPair K V)} {u : Slots w r→ℝ}
  {sel : (Fin w×Bool)→Fin r} {e : I→Fin w} {s : ℝ}
  (W : ReciprocalWindows p u sel e s)

omit [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma support_product (k : ℝ) (hdrop : ∀ i,u (earlySlot sel (e i))-u (lateSlot sel (e i)) ≤ k)
    (i : I) (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) :
    (Nat.card K:ℝ)^5*Real.exp (-(k+2*s+Real.log 4)) ≤
      ((W.firstSupport i A).card:ℝ)*(W.secondSupport i B).card := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hh:=pivot_support_product (Nat.card K) (u (earlySlot sel (e i))) (u (lateSlot sel (e i)))
    s k (W.firstSupport i A).card (W.secondSupport i B).card hq (hdrop i)
    ((W.early i).first_size _ ((W.early i).firstLaw.repair_positive A))
    ((W.late i).second_size _ ((W.late i).secondLaw.repair_positive B))
  have he : Real.exp (-(k+2*s+Real.log 4))=Real.exp (-k-2*s)/4 := by
    rw [show -(k+2*s+Real.log 4)=(-k-2*s)-Real.log 4 by ring,
      Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<4)]
  simpa only [he,mul_div_assoc] using hh

end ReciprocalWindows

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_AllWindowCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Marking Windows
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal
noncomputable section

local instance costBDE_ra79e00_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.ProjectiveIncidence.costIDE
lemma windowCodeBudget_ge_header {σ q P b : ℝ} (w H : ℕ)
    (hσ : 0≤σ) (hq : 0≤q) (hP : 0≤P) (hb : 0≤b) :
    Real.log (w+1)≤windowCodeBudget σ q P b w H := by
  have hc : 0≤nodeChargeConstant := nodeChargeConstant_nonneg
  have hl : 0≤Real.log (320/((9:ℝ)/100000)+320) := Real.log_nonneg (by norm_num)
  unfold windowCodeBudget
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hl4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hh : 0≤(nodeChargeConstant*q*P*H*(3*σ+Real.log 4+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*w)+
      (Real.log 2+nodeChargeConstant*q*P*(b+1+P))*w)+(2*(w:ℝ)+1)*Real.log 2 := by positivity
  linarith

lemma windowCodeBudget_mono {σ q P b G : ℝ} {m w h H : ℕ}
    (_hσ : 0≤σ) (hq : 0≤q) (hP : 0≤P) (hb : 0≤b) (hG : 0≤G)
    (hG' : G≤3*σ+Real.log 4) (hm : m≤w) (hh : h≤H) :
    Real.log (w+1)+
      (nodeChargeConstant*q*P*h*(G+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*m)+
        (Real.log 2+nodeChargeConstant*q*P*(b+1+P))*m)+(2*(m:ℝ)+1)*Real.log 2≤
      windowCodeBudget σ q P b w H := by
  have hc : 0≤nodeChargeConstant := nodeChargeConstant_nonneg
  have hl : 0≤Real.log (320/((9:ℝ)/100000)+320) := Real.log_nonneg (by norm_num)
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hm' : (m:ℝ)≤w := by exact_mod_cast hm
  have hh' : (h:ℝ)≤H := by exact_mod_cast hh
  apply add_le_add
  · apply add_le_add le_rfl
    apply add_le_add
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hh' (by positivity))
        (add_le_add hG' (mul_le_mul_of_nonneg_left hm' (by positivity)))
        (by positivity) (by positivity)
    · exact mul_le_mul_of_nonneg_left hm' (by positivity)
  · exact mul_le_mul_of_nonneg_right (by linarith) hl2

theorem eventually_allWindow_cost_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k s : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (w n H : ℕ) [Nonempty (Fin n)]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n)
      (E : Finset (Fin w))
      (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤k+2*s+Real.log 4 → k+2*s+Real.log 4≤Cb*D*σ^(6*beta η) →
      (∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k) → w<2^H →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card),
      variableTreeCost f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r p u sel E W σ hσ hq hd.le (9/100000) (9/10)
          (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t z)≤
      windowCodeBudget σ (Nat.card K) (P η σ D R) (k+2*s+Real.log 4) w H := by
  filter_upwards [eventually_variable_tree_cost hη hη' Cb hCb] with σ hh
  intro D k s R L₀ q K V _ _ _ _ _ _ _ _ _ hd w n H _ p u sel E W hσ hq
    hcard hr hL hb hbhi hdrop hH
  dsimp only
  let f := fun C : PivotContext K V =>
    fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun C : PivotContext K V =>
    fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
      (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
  intro t z
  have hP : 0≤P η σ D R := le_of_lt (lt_of_lt_of_le (by positivity)
    (finite_bounds hη hη' hσ hr).2.2.2.2.2.1)
  change variableTreeCost f r t _ (allWindowEncoded f r p u sel E W _ _ _ _ _ _ _ _ _ t z)≤_
  unfold allWindowEncoded
  split_ifs with hE
  · have hs := hh D (k+2*s+Real.log 4) R L₀ q K V hd w
      ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩
      (fun i=>(W hE).firstSupport i (z.1 i)) (fun i=>(W hE).secondSupport i (z.2 i))
      (fun i=>(W hE).first_nonempty i _) (fun i=>(W hE).second_nonempty i _) hσ hq
      hcard hr hL hb hbhi
      (fun i=>(W hE).support_product k (fun v=>hdrop _ (survivingOriginal_mem E hE v)) i (z.1 i) (z.2 i))
      t (Finset.univ,Finset.univ)
    apply hs.trans
    exact windowCodeBudget_mono (zero_le_one.trans hσ) (by positivity) hP hb
      (by exact le_max_left _ _) (ambient_pivotPotential hd σ hq)
      (by simpa using Finset.card_le_univ E)
      (finiteBalanced_height H E.card ((lt_of_le_of_lt (by simpa using Finset.card_le_univ E) hH)))
  · rw [variableTreeEmpty_cost]
    exact windowCodeBudget_ge_header w H (zero_le_one.trans hσ) (by positivity) hP hb
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ProjectiveIncidence.eventually_allWindow_cost_oai := @OAI.SharpRamseyFive.ProjectiveIncidence.eventually_allWindow_cost_oai
