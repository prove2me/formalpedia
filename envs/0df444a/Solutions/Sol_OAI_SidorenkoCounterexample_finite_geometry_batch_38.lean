-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_38
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:43:03.40226+00:00
-- url     : https://prove2.me/submissions/04ac24a4-b225-4ba5-b824-33cf453bd59c

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
attribute [local instance] OAI.SidorenkoCounterexample.OrientedKernel.finiteX OAI.SidorenkoCounterexample.OrientedKernel.finiteY OAI.SidorenkoCounterexample.OrientedKernel.nonemptyX OAI.SidorenkoCounterexample.OrientedKernel.nonemptyY
attribute [local instance] OAI.SidorenkoCounterexample.SymmetricCounterKernel.finite OAI.SidorenkoCounterexample.SymmetricCounterKernel.nonempty
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0605]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0646]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0655]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_1000]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_1001]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_1002]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_1004]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_1005]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_1010]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_1013]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_1014]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_1015]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_1020]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_1022]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_1025]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_1214]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_1289]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_1309]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_1311]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_1313]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_1315]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_1320]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_1321]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_1323]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_1324]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_1325]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_1327]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_1328]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_1329]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_1330]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_1333]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35

namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section MatrixActivation
variable {F K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
end MatrixActivation
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Types
variable {K : Type} [Fintype K] [DecidableEq K]
end Types
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Typed
variable {A B K : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
end Typed
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Kernel
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end Kernel
namespace FiniteLaw
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section MatrixMean
variable {F K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K] in
lemma certificate_proof_1334 (r : ℕ) (z : Activation K) (x y : K → SymMatrix F (2*(2*r))) :
    sampleMatrixKernel (2*r) z x y=sampleMatrixKernel (2*r) z y x := by
  unfold sampleMatrixKernel
  apply Finset.prod_congr rfl; intro κ _
  have hc : quadraticChar F ((-1:F)^(2*r))=1 := by rw [Even.neg_one_pow (even_two_mul r)]; simp
  rw [←neg_sub (x κ) (y κ),rankKernel_neg,hc,one_mul]

private instance certificate_instance_1334 : OAI.SidorenkoCounterexample.ProofCertificate_1334 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_1334 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8

lemma certificate_proof_1335 (r : ℕ) (p : FiniteLaw (Activation K)) (x y : K → SymMatrix F (2*(2*r))) :
    activationMatrixKernel (2*r) p x y=activationMatrixKernel (2*r) p y x := by
  apply FiniteLaw.mean_congr; intro z; exact sampleMatrixKernel_symm r z x y

private instance certificate_instance_1335 : OAI.SidorenkoCounterexample.ProofCertificate_1335 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_1335 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end MatrixMean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section TypedMatrix
variable {A B K F : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
  [Field F] [Fintype F] [DecidableEq F]
omit [Fintype A] [Fintype B] in
lemma certificate_proof_1336 (r : ℕ) (p : A → B → FiniteLaw (Activation K))
    (x : A × (K → SymMatrix F (2*r))) (y : B × (K → SymMatrix F (2*r))) :
    0≤typedMatrixKernel r p x y := activationMatrixKernel_nonneg r _ _ _

private instance certificate_instance_1336 : OAI.SidorenkoCounterexample.ProofCertificate_1336 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_1336 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

lemma certificate_proof_1337 (r : ℕ) (π : FiniteLaw A) (ν : FiniteLaw B)
    (p : A → B → FiniteLaw (Activation K)) :
    bipartiteMoment (typedMatrixLaw (F := F) (K := K) r π) (typedMatrixLaw r ν) (typedMatrixKernel r p)=
      (typeMapLaw π ν).mean (fun ab => conditionalMatrixMoment (F := F) r (fun k => p (ab.1 (cornerPoint k)) (ab.2 k.1))) := by
  rw [typedMatrixLaw,typedMatrixLaw,bipartiteMoment_typed]
  apply FiniteLaw.mean_congr; intro ab
  simp_rw [FiniteLaw.independent_uniform_mean]
  rw [conditionalMatrixMoment,uniformMean_prod]
  rfl

private instance certificate_instance_1337 : OAI.SidorenkoCounterexample.ProofCertificate_1337 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_1337 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

lemma certificate_proof_1338 (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
    (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K)) :
    kernelMean (typedMatrixLaw (F := F) (K := K) r π) (typedMatrixLaw r ν) (typedMatrixKernel r p)=1 := by
  rw [typedMatrixLaw,typedMatrixLaw,kernelMean_prod]
  have h (a : A) (b : B) :
      (FiniteLaw.uniform : FiniteLaw (K → SymMatrix F (2*r))).mean (fun x =>
        FiniteLaw.uniform.mean (fun y => typedMatrixKernel r p (a,x) (b,y)))=1 := by
    rw [FiniteLaw.mean_swap]
    simp only [FiniteLaw.mean_uniform,typedMatrixKernel,activationMatrixKernel_mean r hr hF,uniformMean_const]
  simp only [h,FiniteLaw.mean_const]

private instance certificate_instance_1338 : OAI.SidorenkoCounterexample.ProofCertificate_1338 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_1338 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

omit [Fintype A] [Fintype B] in
lemma certificate_proof_1339 (r : ℕ) (p : A → B → FiniteLaw (Activation K))
    (x : A × (K → SymMatrix F (2*(2*r)))) (y : B × (K → SymMatrix F (2*(2*r)))) :
    typedMatrixKernel (2*r) p x y=typedMatrixKernel (2*r) (fun b a => p a b) y x :=
  activationMatrixKernel_symm r _ _ _

private instance certificate_instance_1339 : OAI.SidorenkoCounterexample.ProofCertificate_1339 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_1339 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end TypedMatrix
lemma certificate_proof_1340 {A B K : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
    (r : ℕ) (hl : singularTailThreshold≤2*(2*r)) (π : FiniteLaw A) (ν : FiniteLaw B)
    (p : A → B → FiniteLaw (Activation K))
    (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) :
    Tendsto (fun q : OddPrime => bipartiteMoment
      (typedMatrixLaw (F := ZMod q.val) (K := K) (2*r) π) (typedMatrixLaw (2*r) ν) (typedMatrixKernel (2*r) p))
      primeInfinity (nhds (1+averagedCoefficient π ν p)) := by
  have ht := FiniteLaw.mean_tendsto (typeMapLaw π ν)
    (fun q : OddPrime => fun ab => conditionalMatrixMoment (F := ZMod q.val) (2*r) (fun k => p (ab.1 (cornerPoint k)) (ab.2 k.1)))
    (fun ab => 1+typedCoefficient p ab.1 ab.2)
    (fun ab => conditionalMatrixMoment_tendsto r hl _ (fun k => hp _ _))
  simp only [FiniteLaw.mean_add,FiniteLaw.mean_const] at ht
  simpa only [typedMatrixKernel_moment,averagedCoefficient] using ht

private instance certificate_instance_1340 : OAI.SidorenkoCounterexample.ProofCertificate_1340 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_1340 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]
omit [Fintype A] [Fintype I] [DecidableEq I] in
lemma certificate_proof_1341 : Function.Injective (fun a : I → A => fun i => some (a i)) := by
  intro a b h
  funext i; exact Option.some_injective _ (congrFun h i)

private instance certificate_instance_1341 : OAI.SidorenkoCounterexample.ProofCertificate_1341 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1341 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1

omit [Fintype A] [DecidableEq I] in
lemma certificate_proof_1342 (z : I → Option A) (hz : ∀ a : I → A,(fun i => some (a i))≠z) : ∃ i,z i=none := by
  by_contra hn
  push Not at hn
  have hs (i : I) : ∃ a,z i=some a := by
    cases hi : z i with
    | none => exact False.elim (hn i hi)
    | some a => exact ⟨a,rfl⟩
  exact hz (fun i => (hs i).choose) (funext (fun i => (hs i).choose_spec.symm))

private instance certificate_instance_1342 : OAI.SidorenkoCounterexample.ProofCertificate_1342 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1342 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4

lemma certificate_proof_1343 (p : FiniteLaw A) (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1)
    (f : (I → Option A) → ℝ) (hf : ∀ z,(∃ i,z i=none) → f z=0) :
    (independent (fun _ : I => p.diluted ε h0 h1)).mean f=
      ε^Fintype.card I*(independent (fun _ : I => p)).mean (fun a => f (fun i => some (a i))) := by
  unfold mean independent
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_of_injective (fun a : I → A => fun i => some (a i)) someFunction_injective
  · intro z hz
    rw [hf z (exists_none_of_not_some z (fun a ha => hz ⟨a,ha⟩)),mul_zero]
  · intro a
    simp only [diluted,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    ring

private instance certificate_instance_1343 : OAI.SidorenkoCounterexample.ProofCertificate_1343 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_1343 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Dilution
variable {A B K : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
omit [Fintype A] [Fintype B] in
lemma certificate_proof_1344 (p : A → B → FiniteLaw (Activation K))
    (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) :
    ∀ a b α,α≠∅ → (dilutedPairLaw p a b).mean (activationPhi α)=0 := by
  intro a b α hα; cases a with
  | none => exact inactiveLaw_zero α hα
  | some a => exact hp a b α hα

private instance certificate_instance_1344 : OAI.SidorenkoCounterexample.ProofCertificate_1344 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_1344 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

lemma certificate_proof_1345 (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
    (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) :
    averagedCoefficient (π.diluted ε h0 h1) ν (dilutedPairLaw p)=ε^13*averagedCoefficient π ν p := by
  unfold averagedCoefficient typeMapLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_prod]
  have hz (a : Fin 13 → Option A) (ha : ∃ i,a i=none) :
      (FiniteLaw.independent (fun _ : Fin 22 => ν)).mean (fun b => typedCoefficient (dilutedPairLaw p) a b)=0 := by
    obtain ⟨i,hi⟩ := ha
    have he (b : Fin 22 → B) : typedCoefficient (dilutedPairLaw p) a b=0 :=
      typedCoefficient_inactive_left _ a b i (fun j => by rw [hi]; rfl)
    simp only [he,FiniteLaw.mean_const]
  rw [FiniteLaw.diluted_independent_mean π ε h0 h1 _ hz]
  rfl

private instance certificate_instance_1345 : OAI.SidorenkoCounterexample.ProofCertificate_1345 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_1345 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

lemma certificate_proof_1346 (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
    (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) :
    averagedCoefficient ν (π.diluted ε h0 h1) (fun b a => dilutedPairLaw p a b)=
      ε^22*averagedCoefficient ν π (fun b a => p a b) := by
  unfold averagedCoefficient typeMapLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_prod]
  have hd (b : Fin 13 → B) :
      (FiniteLaw.independent (fun _ : Fin 22 => π.diluted ε h0 h1)).mean
        (fun a => typedCoefficient (fun b a => dilutedPairLaw p a b) b a)=
      ε^22*(FiniteLaw.independent (fun _ : Fin 22 => π)).mean
        (fun a => typedCoefficient (fun b a => p a b) b a) := by
    apply FiniteLaw.diluted_independent_mean
    intro a ha
    obtain ⟨j,hj⟩ := ha
    exact typedCoefficient_inactive_right _ b a j (fun i => by rw [hj]; rfl)
  simp only [hd,FiniteLaw.mean_mul]

private instance certificate_instance_1346 : OAI.SidorenkoCounterexample.ProofCertificate_1346 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_1346 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Dilution
lemma certificate_proof_1347 (t0 t1 : ℝ) (hneg : t0<0) :
    ∃ ε : ℝ,0<ε ∧ ε<1 ∧ (1+ε^13*t0)*(1+ε^22*t1)<1 := by
  let f := fun ε : ℝ => t0+ε^9*t1+ε^22*t0*t1
  have hl : Tendsto f (nhds 0) (nhds t0) := by
    have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
    simpa only [f,zero_pow (by omega : 9≠0),zero_pow (by omega : 22≠0),zero_mul,add_zero] using hc.tendsto
  have he : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),f ε<0 :=
    (hl.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hneg)
  have hlt : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),ε<1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hpos : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hε1,hε0⟩ := (he.and (hlt.and hpos)).exists
  refine ⟨ε,hε0,hε1,?_⟩
  have halg : (1+ε^13*t0)*(1+ε^22*t1)=1+ε^13*f ε := by dsimp [f]; ring
  rw [halg]
  exact add_lt_of_neg_right 1 (mul_neg_of_pos_of_neg (pow_pos hε0 _) hε)

private instance certificate_instance_1347 : OAI.SidorenkoCounterexample.ProofCertificate_1347 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1347 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section PinningRound
variable {I J E C : Type} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
end PinningRound
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Mix
variable {A : Type} [Fintype A]
end Mix
section Pin
variable {I J E C : Type} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
end Pin
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Weights
variable {A I : Type} [Fintype A] [Nonempty A] [Fintype I]
lemma certificate_proof_1348 (s : A → ℝ) (ρ : ℝ) : 0<exponentialNormalizer s ρ :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

private instance certificate_instance_1348 : OAI.SidorenkoCounterexample.ProofCertificate_1348 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1348 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4

lemma certificate_proof_1349 (ρ : ℝ) (s : I → ℝ) :
    (∏ i,Real.exp (ρ*s i))=Real.exp (ρ*∑ i,s i) := by
  rw [Finset.mul_sum,Real.exp_sum]

private instance certificate_instance_1349 : OAI.SidorenkoCounterexample.ProofCertificate_1349 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1349 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3

lemma certificate_proof_1350 (s : A → ℝ) (ρ : ℝ) (a : I → A) :
    (∏ i,(exponentialPrior s ρ).weight (a i))=
      Real.exp (ρ*∑ i,s (a i))/(exponentialNormalizer s ρ)^Fintype.card I := by
  simp only [exponentialPrior,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,prod_exp_weight]

private instance certificate_instance_1350 : OAI.SidorenkoCounterexample.ProofCertificate_1350 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_1350 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7

omit [Nonempty A] in
lemma certificate_proof_1351 (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀) :
    Tendsto (fun ρ : ℝ => ∑ a,c a*Real.exp (ρ*(s a-s a₀))) atTop (nhds (c a₀)) := by
  have h (a : A) : Tendsto (fun ρ : ℝ => c a*Real.exp (ρ*(s a-s a₀))) atTop
      (nhds (if a=a₀ then c a₀ else 0)) := by
    by_cases ha : a=a₀
    · subst a; simp
    · have hd : s a-s a₀<0 := sub_neg.mpr (hs a ha)
      have ht := Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg hd (tendsto_id : Tendsto (fun ρ : ℝ => ρ) atTop atTop))
      simpa only [ha,ite_false,mul_comm,mul_zero,Function.comp_def,id_eq] using ht.const_mul (c a)
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using tendsto_finsetSum Finset.univ (fun a _ => h a)

private instance certificate_instance_1351 : OAI.SidorenkoCounterexample.ProofCertificate_1351 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1351 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5

omit [Nonempty A] in
lemma certificate_proof_1352 (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀)
    (hc : c a₀<0) : ∃ ρ : ℝ,0<ρ ∧ (∑ a,c a*Real.exp (ρ*s a))<0 := by
  have hlim := exponential_dominant_limit s c a₀ hs
  have he := (hlim.eventually (gt_mem_nhds hc)).and (eventually_gt_atTop 0)
  obtain ⟨ρ,hρ,hpos⟩ := he.exists
  refine ⟨ρ,hpos,?_⟩
  have halg : (∑ a,c a*Real.exp (ρ*s a))=
      Real.exp (ρ*s a₀)*(∑ a,c a*Real.exp (ρ*(s a-s a₀))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [mul_left_comm,←Real.exp_add]
    congr 2; ring
  rw [halg]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hρ

private instance certificate_instance_1352 : OAI.SidorenkoCounterexample.ProofCertificate_1352 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1352 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6

end Weights
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Gibbs
variable {I J E : Type} [Fintype I] [Fintype J] [Fintype E] [Nonempty I] [Nonempty J]
omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
lemma certificate_proof_1353 (s : VertexPairScores I J) (ρ M : ℝ) (a : I) (b : J) :
    0<gibbsThinning s ρ M a b := Real.exp_pos _

private instance certificate_instance_1353 : OAI.SidorenkoCounterexample.ProofCertificate_1353 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1353 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6

omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
lemma certificate_proof_1354 (s : VertexPairScores I J) (ρ M : ℝ) (hρ : 0≤ρ)
    (hM : ∀ a b,s.pair a b≤M) (a : I) (b : J) : gibbsThinning s ρ M a b≤1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonneg_of_nonpos hρ (sub_nonpos.mpr (hM a b))

private instance certificate_instance_1354 : OAI.SidorenkoCounterexample.ProofCertificate_1354 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_1354 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8

lemma certificate_proof_1355 (s : VertexPairScores I J) (ρ M : ℝ) (n : ℕ) : 0<gibbsPrefactor s ρ M n := by
  unfold gibbsPrefactor
  exact div_pos (Real.exp_pos _) (mul_pos (pow_pos (exponentialNormalizer_pos _ _) _) (pow_pos (exponentialNormalizer_pos _ _) _))

private instance certificate_instance_1355 : OAI.SidorenkoCounterexample.ProofCertificate_1355 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1355 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

lemma certificate_proof_1356 (s : VertexPairScores I J) (ρ M : ℝ) (t : E → I) (h : E → J)
    (a : I → I) (b : J → J) :
    (∏ i,(exponentialPrior s.left ρ).weight (a i))*(∏ j,(exponentialPrior s.right ρ).weight (b j))*
        (∏ e,gibbsThinning s ρ M (a (t e)) (b (h e)))=
      gibbsPrefactor s ρ M (Fintype.card E)*Real.exp (ρ*s.score t h a b) := by
  simp only [exponentialPrior_product,gibbsThinning,prod_exp_weight]
  rw [div_mul_div_comm,div_mul_eq_mul_div,mul_assoc,←Real.exp_add,←Real.exp_add]
  unfold gibbsPrefactor
  rw [div_mul_eq_mul_div,←Real.exp_add]
  congr 2
  simp only [VertexPairScores.score,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

private instance certificate_instance_1356 : OAI.SidorenkoCounterexample.ProofCertificate_1356 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_1356 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end Gibbs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
lemma certificate_proof_1357 (s : VertexPairScores (Fin 13) (Fin 22)) (ρ M : ℝ)
    (h0 : ∀ a b,0≤gibbsThinning s ρ M a b) (h1 : ∀ a b,gibbsThinning s ρ M a b≤1) :
    averagedCoefficient (exponentialPrior s.left ρ) (exponentialPrior s.right ρ)
      (fun a b => thinnedLaw (basePairLaw a b) (gibbsThinning s ρ M a b) (h0 a b) (h1 a b))=
      gibbsPrefactor s ρ M 66*(∑ m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22),
        typedCoefficient basePairLaw m.1 m.2*Real.exp (ρ*s.score cornerPoint (fun k : ActCorner => k.1) m.1 m.2)) := by
  unfold averagedCoefficient FiniteLaw.mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _
  dsimp only
  rw [typedCoefficient_thinned]
  change ((∏ i,(exponentialPrior s.left ρ).weight (m.1 i))*(∏ j,(exponentialPrior s.right ρ).weight (m.2 j)))*
    ((∏ k : ActCorner,gibbsThinning s ρ M (m.1 (cornerPoint k)) (m.2 k.1))*typedCoefficient basePairLaw m.1 m.2)=_
  rw [←mul_assoc,gibbs_weight_formula]
  have hc : Fintype.card ActCorner=66 := by decide
  rw [hc]; ring

private instance certificate_instance_1357 : OAI.SidorenkoCounterexample.ProofCertificate_1357 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 c7 q0 q1 q2 q3 q4
  exact @certificate_proof_1357 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4

lemma certificate_proof_1358 : ∃ (π : FiniteLaw (Fin 13)) (ν : FiniteLaw (Fin 22))
    (p : Fin 13 → Fin 22 → FiniteLaw (Activation ActCorner)),
    (∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) ∧ averagedCoefficient π ν p<0 := by
  obtain ⟨s,hs⟩ := pinning_complex
  let Q := fun m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22) => s.score cornerPoint (fun k : ActCorner => k.1) m.1 m.2
  let C := fun m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22) => typedCoefficient basePairLaw m.1 m.2
  have hc : C (id,id)<0 := by
    change activeCoefficient (fun k => activationMoment (basePairLaw (cornerPoint k) k.1))<0
    rw [basePairLaw_identity]; exact neg_neg_of_pos (pow_pos (by norm_num) _)
  obtain ⟨ρ,hρ,hneg⟩ := exponential_dominant_negative Q C (id,id) (fun m hm => hs m.1 m.2 hm) hc
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun ab : Fin 13 × Fin 22 => s.pair ab.1 ab.2)
  have hM (a : Fin 13) (b : Fin 22) : s.pair a b≤M := Finset.le_sup' (fun ab : Fin 13 × Fin 22 => s.pair ab.1 ab.2) (Finset.mem_univ (a,b))
  have h0 (a : Fin 13) (b : Fin 22) : 0≤gibbsThinning s ρ M a b := (gibbsThinning_pos s ρ M a b).le
  have h1 (a : Fin 13) (b : Fin 22) : gibbsThinning s ρ M a b≤1 := gibbsThinning_le_one s ρ M hρ.le hM a b
  refine ⟨exponentialPrior s.left ρ,exponentialPrior s.right ρ,
    (fun a b => thinnedLaw (basePairLaw a b) (gibbsThinning s ρ M a b) (h0 a b) (h1 a b)),?_,?_⟩
  · intro a b α hα
    exact thinnedLaw_zero _ (basePairLaw_zero a b) _ _ _ α hα
  · rw [averagedCoefficient_gibbs]
    exact mul_neg_of_pos_of_neg (gibbsPrefactor_pos s ρ M 66) hneg

private instance certificate_instance_1358 : OAI.SidorenkoCounterexample.ProofCertificate_1358 := by
  constructor
  exact @certificate_proof_1358 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35

end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
lemma certificate_proof_1359 : Nonempty OrientedKernel := by
  obtain ⟨π,ν,p,hp,hneg⟩ := exists_negative_coefficient
  obtain ⟨ε,hε,hε1,hgap⟩ := exists_dilution_gap (averagedCoefficient π ν p)
    (averagedCoefficient ν π (fun b a => p a b)) hneg
  let π' := π.diluted ε hε.le hε1.le
  let p' := dilutedPairLaw p
  have hp' := dilutedPairLaw_zero p hp
  let r := singularTailThreshold
  have hl : singularTailThreshold≤2*(2*r) := by dsimp [r]; omega
  have hr : 0<2*r := by have := singularTailThreshold_large; dsimp [r]; omega
  have ht0 := typedMatrixKernel_tendsto r hl π' ν p' hp'
  have ht1 := typedMatrixKernel_tendsto r hl ν π' (fun b a => p' a b) (fun b a => hp' a b)
  have ht := ht0.mul ht1
  have hcoef : (1+averagedCoefficient π' ν p')*(1+averagedCoefficient ν π' (fun b a => p' a b))<1 := by
    simpa only [π',p',coefficient_dilution_left,coefficient_dilution_right] using hgap
  obtain ⟨q,hq⟩ := (ht.eventually (gt_mem_nhds hcoef)).exists
  let L := typedMatrixLaw (F := ZMod q.val) (K := ActCorner) (2*r) π'
  let R := typedMatrixLaw (F := ZMod q.val) (K := ActCorner) (2*r) ν
  let W := typedMatrixKernel (F := ZMod q.val) (2*r) p'
  have hc : ringChar (ZMod q.val)≠2 := by simpa only [ZMod.ringChar_zmod_n] using q.property.2
  refine ⟨{ X := Option (Fin 13) × (ActCorner → SymMatrix (ZMod q.val) (2*(2*r)))
            Y := Fin 22 × (ActCorner → SymMatrix (ZMod q.val) (2*(2*r)))
            left := L
            right := R
            value := W
            nonneg := typedMatrixKernel_nonneg (2*r) p'
            mean_one := typedMatrixKernel_mean (2*r) hr hc π' ν p'
            gap := ?_ }⟩
  have he : bipartiteMoment R L (fun y x => W x y)=
      bipartiteMoment R L (typedMatrixKernel (F := ZMod q.val) (2*r) (fun b a => p' a b)) := by
    apply bipartiteMoment_congr
    intro y x; exact typedMatrixKernel_transpose r p' x y
  rw [he]; exact hq

private instance certificate_instance_1359 : OAI.SidorenkoCounterexample.ProofCertificate_1359 := by
  constructor
  exact @certificate_proof_1359 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Cross
variable {A B C D X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X] [Fintype Y]
lemma certificate_proof_1360 (p : FiniteLaw A) (q : FiniteLaw B) (r : FiniteLaw C) (s : FiniteLaw D)
    (f : A → D → ℝ) (g : C → B → ℝ) :
    p.mean (fun a => q.mean (fun b => r.mean (fun c => s.mean (fun d => f a d*g c b))))=
      p.mean (fun a => s.mean (f a))*r.mean (fun c => q.mean (g c)) := by
  simp_rw [FiniteLaw.mean_mul_right,FiniteLaw.mean_mul,FiniteLaw.mean_mul_right]
  rw [FiniteLaw.mean_swap q r]

private instance certificate_instance_1360 : OAI.SidorenkoCounterexample.ProofCertificate_1360 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_1360 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

omit [Fintype X] [Fintype Y] in
lemma certificate_proof_1361 (W : X → Y → ℝ) (x y : X × Y) : crossedKernel W x y=crossedKernel W y x := mul_comm _ _

private instance certificate_instance_1361 : OAI.SidorenkoCounterexample.ProofCertificate_1361 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1361 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4

omit [Fintype X] [Fintype Y] in
lemma certificate_proof_1362 (W : X → Y → ℝ) (hW : ∀ x y,0≤W x y) (x y : X × Y) : 0≤crossedKernel W x y :=
  mul_nonneg (hW _ _) (hW _ _)

private instance certificate_instance_1362 : OAI.SidorenkoCounterexample.ProofCertificate_1362 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1362 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5

lemma certificate_proof_1363 (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) :
    kernelMean (π.prod ν) (π.prod ν) (crossedKernel W)=(kernelMean π ν W)^2 := by
  unfold kernelMean
  simp_rw [FiniteLaw.mean_prod]
  simp only [crossedKernel]
  rw [four_means_factor]
  ring

private instance certificate_instance_1363 : OAI.SidorenkoCounterexample.ProofCertificate_1363 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1363 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6

lemma certificate_proof_1364 (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) :
    bipartiteMoment (π.prod ν) (π.prod ν) (crossedKernel W)=
      bipartiteMoment π ν W*bipartiteMoment ν π (fun y x => W x y) := by
  rw [bipartiteMoment_typed]
  unfold typeMapLaw
  rw [FiniteLaw.mean_prod]
  simp only [crossedKernel,Finset.prod_mul_distrib]
  rw [four_means_factor]
  rfl

private instance certificate_instance_1364 : OAI.SidorenkoCounterexample.ProofCertificate_1364 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1364 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6

lemma certificate_proof_1365 (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) (c : ℝ) :
    kernelMean π ν (fun x y => W x y/c)=kernelMean π ν W/c := by
  simp only [kernelMean,div_eq_mul_inv,FiniteLaw.mean_mul_right]

private instance certificate_instance_1365 : OAI.SidorenkoCounterexample.ProofCertificate_1365 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_1365 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7

lemma certificate_proof_1366 (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) (c : ℝ) :
    bipartiteMoment π ν (fun x y => W x y/c)=bipartiteMoment π ν W/c^66 := by
  have hc : Fintype.card ActCorner=66 := by decide
  unfold bipartiteMoment
  simp_rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,hc,div_eq_mul_inv,FiniteLaw.mean_mul_right]

private instance certificate_instance_1366 : OAI.SidorenkoCounterexample.ProofCertificate_1366 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_1366 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7

end Cross
lemma certificate_proof_1367 : Nonempty SymmetricCounterKernel := by
  obtain ⟨W⟩ := exists_oriented_kernel
  let Ω := W.X × W.Y
  let p := W.left.prod W.right
  let V := crossedKernel W.value
  let L : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun xy : Ω × Ω => V xy.1 xy.2)
  have hL (x y : Ω) : V x y≤L := Finset.le_sup' (fun xy : Ω × Ω => V xy.1 xy.2) (Finset.mem_univ (x,y))
  have hmean : kernelMean p p V=1 := by rw [crossedKernel_mean,W.mean_one,one_pow]
  have hone : 1≤L := by
    rw [←hmean]
    exact p.mean_bound (fun x => p.mean_bound (fun y => hL x y))
  have hpos : 0<L := lt_of_lt_of_le zero_lt_one hone
  refine ⟨{ Ω := Ω
            law := p
            value := fun x y => V x y/L
            nonneg := fun x y => div_nonneg (crossedKernel_nonneg _ W.nonneg x y) hpos.le
            le_one := fun x y => (div_le_one hpos).mpr (hL x y)
            symm := fun x y => congrArg (fun z => z/L) (crossedKernel_symm _ x y)
            mean_pos := ?_
            gap := ?_ }⟩
  · rw [kernelMean_div,hmean]; exact div_pos zero_lt_one hpos
  · rw [bipartiteMoment_div,kernelMean_div,hmean,div_pow,one_pow]
    apply (div_lt_div_iff_of_pos_right (pow_pos hpos 66)).mpr
    rw [crossedKernel_moment]; exact W.gap

private instance certificate_instance_1367 : OAI.SidorenkoCounterexample.ProofCertificate_1367 := by
  constructor
  exact @certificate_proof_1367 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
section Marginal
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
lemma certificate_proof_1368 (p : I ⊕ J → FiniteLaw A) (f : (I ⊕ J → A) → ℝ) :
    (independent p).mean f=(independent (fun i => p (.inl i))).mean (fun x =>
      (independent (fun j => p (.inr j))).mean (fun y => f (Sum.elim x y))) := by
  unfold mean independent
  simp only [Finset.mul_sum]
  rw [←Fintype.sum_prod_type (fun xy : (I → A) × (J → A) =>
    (∏ i,(p (.inl i)).weight (xy.1 i))*((∏ j,(p (.inr j)).weight (xy.2 j))*f (Sum.elim xy.1 xy.2)))]
  apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow I J A)
  intro x
  simp only [Fintype.prod_sum_type,Equiv.sumArrowEquivProdArrow,Equiv.coe_fn_mk]
  have he : Sum.elim (fun i => x (.inl i)) (fun j => x (.inr j))=x := by funext ij; cases ij <;> rfl
  change _ = (∏ i,(p (.inl i)).weight (x (.inl i)))*
    ((∏ j,(p (.inr j)).weight (x (.inr j)))*f (Sum.elim (fun i => x (.inl i)) (fun j => x (.inr j))))
  rw [he]; ring

private instance certificate_instance_1368 : OAI.SidorenkoCounterexample.ProofCertificate_1368 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1368 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

lemma certificate_proof_1369 (p : J → FiniteLaw A) (e : I → J) (he : Function.Injective e)
    (f : (I → A) → ℝ) :
    (independent p).mean (fun x => f (fun i => x (e i)))=(independent (fun i => p (e i))).mean f := by
  let E : I ⊕ {j : J // j∉Set.range e} ≃ J :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range e))
  have hE (i : I) : E (.inl i)=e i := rfl
  have h := independent_mean_equiv E p (fun x => f (fun i => x (e i)))
  rw [←h,independent_mean_sum]
  have hi (x : I → A) (y : {j : J // j∉Set.range e} → A) :
      (fun i => Sum.elim x y (E.symm (e i)))=x := by
    funext i; rw [←hE i,E.symm_apply_apply]; rfl
  simp only [hi,mean_const,hE]

private instance certificate_instance_1369 : OAI.SidorenkoCounterexample.ProofCertificate_1369 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_1369 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

lemma certificate_proof_1370 (p : FiniteLaw A) (q : A → FiniteLaw B) (f : B → ℝ) :
    (p.bind q).mean f=p.mean (fun a => (q a).mean f) := by
  simp only [mean,bind,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

private instance certificate_instance_1370 : OAI.SidorenkoCounterexample.ProofCertificate_1370 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1370 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5 q6

lemma certificate_proof_1371 (p : FiniteLaw A) (f : A → ℝ) (hf : ∀ a,0≤f a) (n : ℕ) :
    (p.mean f)^n≤p.mean (fun a => (f a)^n) := by
  simpa only [mean,smul_eq_mul] using (convexOn_pow (𝕜 := ℝ) n).map_sum_le
    (t := Finset.univ) (w := p.weight) (p := f) (fun a _ => p.nonneg a) p.total (fun a _ => hf a)

private instance certificate_instance_1371 : OAI.SidorenkoCounterexample.ProofCertificate_1371 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1371 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 q0 q1 q2 q3 q4 q5

end Marginal
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_1334 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1335 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1336 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1337 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1338 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1339 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1340 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1341 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1342 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1343 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1344 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1345 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1346 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1347 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1348 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1349 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1350 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1351 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1352 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1353 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1354 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1355 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1356 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1357 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1358 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1359 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1360 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1361 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1362 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1363 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1364 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1365 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1366 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1367 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1368 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1369 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1370 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1371 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

