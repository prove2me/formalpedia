-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_39
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:44:55.793891+00:00
-- url     : https://prove2.me/submissions/ac949beb-8069-48d8-abb0-aa347aef2fd0

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
attribute [local instance] OAI.SidorenkoCounterexample.OrientedKernel.finiteX OAI.SidorenkoCounterexample.OrientedKernel.finiteY OAI.SidorenkoCounterexample.OrientedKernel.nonemptyX OAI.SidorenkoCounterexample.OrientedKernel.nonemptyY
attribute [local instance] OAI.SidorenkoCounterexample.SymmetricCounterKernel.finite OAI.SidorenkoCounterexample.SymmetricCounterKernel.nonempty
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0439]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_1009]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_1291]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_1368]
include p0 p1 p2 p3

namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Cross
variable {A B C D X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X] [Fintype Y]
end Cross
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
section Marginal
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
lemma certificate_proof_1372 (p : FiniteLaw A) {f g : A → ℝ} (h : p.mean f<p.mean g) : ∃ a,f a<g a := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt h) (p.mean_mono hn)

private instance certificate_instance_1372 : OAI.SidorenkoCounterexample.ProofCertificate_1372 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1372 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5

end Marginal
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
lemma certificate_proof_1373 {V : Type} (G : SimpleGraph V) (a b : V) : 0≤edgeIndicator G a b := by
  unfold edgeIndicator; split <;> norm_num

private instance certificate_instance_1373 : OAI.SidorenkoCounterexample.ProofCertificate_1373 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1373 p0 p1 p2 p3 q0 q1 q2 q3

lemma certificate_proof_1374 {V : Type} (G : SimpleGraph V) (a b : V) : edgeIndicator G a b≤1 := by
  unfold edgeIndicator; split <;> norm_num

private instance certificate_instance_1374 : OAI.SidorenkoCounterexample.ProofCertificate_1374 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1374 p0 p1 p2 p3 q0 q1 q2 q3

lemma certificate_proof_1375 {V : Type} (G : SimpleGraph V) (a b : V) : edgeIndicator G a b=edgeIndicator G b a := by
  simp only [edgeIndicator,G.adj_comm]

private instance certificate_instance_1375 : OAI.SidorenkoCounterexample.ProofCertificate_1375 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1375 p0 p1 p2 p3 q0 q1 q2 q3

lemma certificate_proof_1376 (j : Fin 22) (i : Fin 13) : i∈faces j ↔ ∃ r,faceVertex j r=i := by
  rw [faceVertex_correct]
  constructor
  · simp only [Finset.mem_insert,Finset.mem_singleton]
    rintro (h|h|h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
  · rintro ⟨r,rfl⟩; fin_cases r <;> simp

private instance certificate_instance_1376 : OAI.SidorenkoCounterexample.ProofCertificate_1376 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1376 p0 p1 p2 p3 q0 q1

lemma certificate_proof_1377 {V : Type} (G : SimpleGraph V) (f : PatternVertex → V) :
    (∀ u v,H.Adj u v → G.Adj (f u) (f v)) ↔
      ∀ k : ActCorner,G.Adj (f (.inl (cornerPoint k))) (f (.inr k.1)) := by
  constructor
  · intro h k; exact h _ _ (faceVertex_mem k.1 k.2)
  · intro h u v huv
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim huv
      | inr j =>
        obtain ⟨r,hr⟩ := (mem_faces_iff j i).mp huv
        simpa only [cornerPoint,hr] using h (j,r)
    | inr j =>
      cases v with
      | inl i =>
        obtain ⟨r,hr⟩ := (mem_faces_iff j i).mp huv
        simpa only [cornerPoint,hr] using (h (j,r)).symm
      | inr j' => exact False.elim huv

private instance certificate_instance_1377 : OAI.SidorenkoCounterexample.ProofCertificate_1377 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1377 p0 p1 p2 p3 q0 q1 q2

lemma certificate_proof_1378 {V : Type} (G : SimpleGraph V) (f : PatternVertex → V) :
    homIndicator G f=if ∀ u v,H.Adj u v → G.Adj (f u) (f v) then 1 else 0 := by
  simp only [homIndicator,edgeIndicator,Fintype.prod_boole,hom_iff_corners]

private instance certificate_instance_1378 : OAI.SidorenkoCounterexample.ProofCertificate_1378 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1378 p0 p1 p2 p3 q0 q1 q2

lemma certificate_proof_1379 {V : Type} (G : SimpleGraph V) (f : PatternVertex → V) : 0≤homIndicator G f := by
  rw [homIndicator_eq]; split <;> norm_num

private instance certificate_instance_1379 : OAI.SidorenkoCounterexample.ProofCertificate_1379 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1379 p0 p1 p2 p3 q0 q1 q2

lemma certificate_proof_1380 {V : Type} (G : SimpleGraph V) (f : PatternVertex → V) : homIndicator G f≤1 := by
  rw [homIndicator_eq]; split <;> norm_num

private instance certificate_instance_1380 : OAI.SidorenkoCounterexample.ProofCertificate_1380 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1380 p0 p1 p2 p3 q0 q1 q2

lemma certificate_proof_1381 {V : Type} [Fintype V] (G : SimpleGraph V) :
    homDensity H G=uniformMean (homIndicator G) := by
  unfold homDensity homCount uniformMean
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun,homIndicator_eq,Nat.cast_pow]
  congr 1
  simp [Fintype.card_subtype]

private instance certificate_instance_1381 : OAI.SidorenkoCounterexample.ProofCertificate_1381 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1381 p0 p1 p2 p3 q0 q1 q2

lemma certificate_proof_1382 {V : Type} [Fintype V] (G : SimpleGraph V) :
    edgeDensity G=uniformMean (fun ab : V × V => edgeIndicator G ab.1 ab.2) := by
  have hs : (∑ a,∑ b,edgeIndicator G a b)=(2*(Fintype.card G.edgeSet) : ℕ) := by
    calc
      _ = ∑ a,(G.degree a : ℝ) := by
        apply Finset.sum_congr rfl; intro a _
        simp [edgeIndicator,←G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter]
      _ = _ := by exact_mod_cast (G.sum_degrees_eq_twice_card_edges.trans (congrArg (2*·) G.edgeFinset_card))
  unfold edgeDensity uniformMean
  rw [Fintype.sum_prod_type,hs]
  simp only [Nat.card_eq_fintype_card,Fintype.card_prod,Nat.cast_mul,Nat.cast_ofNat]
  congr 1; ring

private instance certificate_instance_1382 : OAI.SidorenkoCounterexample.ProofCertificate_1382 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1382 p0 p1 p2 p3 q0 q1 q2

lemma certificate_proof_1383 {V : Type} (G : SimpleGraph V) : 0≤homDensity H G := by
  unfold homDensity; positivity

private instance certificate_instance_1383 : OAI.SidorenkoCounterexample.ProofCertificate_1383 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1383 p0 p1 p2 p3 q0 q1

lemma certificate_proof_1384 {V : Type} (G : SimpleGraph V) : 0≤edgeDensity G := by
  unfold edgeDensity; positivity

private instance certificate_instance_1384 : OAI.SidorenkoCounterexample.ProofCertificate_1384 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1384 p0 p1 p2 p3 q0 q1

lemma certificate_proof_1385 {V : Type} [Fintype V] (G : SimpleGraph V)
    (h : ∀ a b,¬G.Adj a b) : edgeDensity G=0 := by
  rw [edgeDensity_eq_mean]; simp [uniformMean,edgeIndicator,h]

private instance certificate_instance_1385 : OAI.SidorenkoCounterexample.ProofCertificate_1385 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1385 p0 p1 p2 p3 q0 q1 q2 q3

lemma certificate_proof_1386 {A : Type} [Fintype A] (π : FiniteLaw A) (U : A → A → ℝ) :
    (FiniteLaw.independent (fun _ : PatternVertex => π)).mean (fun z =>
      ∏ k : ActCorner,U (z (.inl (cornerPoint k))) (z (.inr k.1)))=bipartiteMoment π π U := by
  rw [FiniteLaw.independent_mean_sum]; rfl

private instance certificate_instance_1386 : OAI.SidorenkoCounterexample.ProofCertificate_1386 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1386 p0 p1 p2 p3 q0 q1 q2 q3

end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_1372 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1373 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1374 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1375 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1376 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1377 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1378 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1379 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1380 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1381 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1382 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1383 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1384 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1385 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1386 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

