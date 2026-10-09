-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_36
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:40:51.49196+00:00
-- url     : https://prove2.me/submissions/cc8a987c-7eba-4327-9988-72ffa342971e

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0377]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0439]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0919]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_1000]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_1006]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_1016]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_1072]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_1073]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_1224]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_1230]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_1232]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_1233]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_1234]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section Coefficients
variable {K : Type} [Fintype K] [DecidableEq K]
end Coefficients
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type} [Fintype K] [DecidableEq K]
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
theorem certificate_proof_1235 : ∀ j k,pairFace (facePair j k) (faceSide j k)=j := by decide

private instance certificate_instance_1235 : OAI.SidorenkoCounterexample.ProofCertificate_1235 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1235 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1

theorem certificate_proof_1236 : ∀ j k,faceSlot (facePair j k) (faceSide j k)=k := by decide

private instance certificate_instance_1236 : OAI.SidorenkoCounterexample.ProofCertificate_1236 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1236 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1

theorem certificate_proof_1237 : ∀ e b,faceSide (pairFace e b) (faceSlot e b)=b := by decide

private instance certificate_instance_1237 : OAI.SidorenkoCounterexample.ProofCertificate_1237 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1237 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1

lemma certificate_proof_1238 : Finset.univ.image (pairCorner 0)=pairCorners 0 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1238 : OAI.SidorenkoCounterexample.ProofCertificate_1238 := by
  constructor
  exact @certificate_proof_1238 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1239 : Finset.univ.image (pairCorner 1)=pairCorners 1 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1239 : OAI.SidorenkoCounterexample.ProofCertificate_1239 := by
  constructor
  exact @certificate_proof_1239 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1240 : Finset.univ.image (pairCorner 2)=pairCorners 2 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1240 : OAI.SidorenkoCounterexample.ProofCertificate_1240 := by
  constructor
  exact @certificate_proof_1240 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1241 : Finset.univ.image (pairCorner 3)=pairCorners 3 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1241 : OAI.SidorenkoCounterexample.ProofCertificate_1241 := by
  constructor
  exact @certificate_proof_1241 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1242 : Finset.univ.image (pairCorner 4)=pairCorners 4 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1242 : OAI.SidorenkoCounterexample.ProofCertificate_1242 := by
  constructor
  exact @certificate_proof_1242 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1243 : Finset.univ.image (pairCorner 5)=pairCorners 5 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1243 : OAI.SidorenkoCounterexample.ProofCertificate_1243 := by
  constructor
  exact @certificate_proof_1243 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1244 : Finset.univ.image (pairCorner 6)=pairCorners 6 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1244 : OAI.SidorenkoCounterexample.ProofCertificate_1244 := by
  constructor
  exact @certificate_proof_1244 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1245 : Finset.univ.image (pairCorner 7)=pairCorners 7 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1245 : OAI.SidorenkoCounterexample.ProofCertificate_1245 := by
  constructor
  exact @certificate_proof_1245 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1246 : Finset.univ.image (pairCorner 8)=pairCorners 8 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1246 : OAI.SidorenkoCounterexample.ProofCertificate_1246 := by
  constructor
  exact @certificate_proof_1246 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1247 : Finset.univ.image (pairCorner 9)=pairCorners 9 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1247 : OAI.SidorenkoCounterexample.ProofCertificate_1247 := by
  constructor
  exact @certificate_proof_1247 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1248 : Finset.univ.image (pairCorner 10)=pairCorners 10 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1248 : OAI.SidorenkoCounterexample.ProofCertificate_1248 := by
  constructor
  exact @certificate_proof_1248 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1249 : Finset.univ.image (pairCorner 11)=pairCorners 11 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1249 : OAI.SidorenkoCounterexample.ProofCertificate_1249 := by
  constructor
  exact @certificate_proof_1249 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1250 : Finset.univ.image (pairCorner 12)=pairCorners 12 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1250 : OAI.SidorenkoCounterexample.ProofCertificate_1250 := by
  constructor
  exact @certificate_proof_1250 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1251 : Finset.univ.image (pairCorner 13)=pairCorners 13 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1251 : OAI.SidorenkoCounterexample.ProofCertificate_1251 := by
  constructor
  exact @certificate_proof_1251 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1252 : Finset.univ.image (pairCorner 14)=pairCorners 14 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1252 : OAI.SidorenkoCounterexample.ProofCertificate_1252 := by
  constructor
  exact @certificate_proof_1252 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1253 : Finset.univ.image (pairCorner 15)=pairCorners 15 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1253 : OAI.SidorenkoCounterexample.ProofCertificate_1253 := by
  constructor
  exact @certificate_proof_1253 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1254 : Finset.univ.image (pairCorner 16)=pairCorners 16 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1254 : OAI.SidorenkoCounterexample.ProofCertificate_1254 := by
  constructor
  exact @certificate_proof_1254 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1255 : Finset.univ.image (pairCorner 17)=pairCorners 17 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1255 : OAI.SidorenkoCounterexample.ProofCertificate_1255 := by
  constructor
  exact @certificate_proof_1255 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1256 : Finset.univ.image (pairCorner 18)=pairCorners 18 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1256 : OAI.SidorenkoCounterexample.ProofCertificate_1256 := by
  constructor
  exact @certificate_proof_1256 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1257 : Finset.univ.image (pairCorner 19)=pairCorners 19 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1257 : OAI.SidorenkoCounterexample.ProofCertificate_1257 := by
  constructor
  exact @certificate_proof_1257 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1258 : Finset.univ.image (pairCorner 20)=pairCorners 20 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1258 : OAI.SidorenkoCounterexample.ProofCertificate_1258 := by
  constructor
  exact @certificate_proof_1258 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1259 : Finset.univ.image (pairCorner 21)=pairCorners 21 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1259 : OAI.SidorenkoCounterexample.ProofCertificate_1259 := by
  constructor
  exact @certificate_proof_1259 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1260 : Finset.univ.image (pairCorner 22)=pairCorners 22 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1260 : OAI.SidorenkoCounterexample.ProofCertificate_1260 := by
  constructor
  exact @certificate_proof_1260 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1261 : Finset.univ.image (pairCorner 23)=pairCorners 23 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1261 : OAI.SidorenkoCounterexample.ProofCertificate_1261 := by
  constructor
  exact @certificate_proof_1261 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1262 : Finset.univ.image (pairCorner 24)=pairCorners 24 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1262 : OAI.SidorenkoCounterexample.ProofCertificate_1262 := by
  constructor
  exact @certificate_proof_1262 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1263 : Finset.univ.image (pairCorner 25)=pairCorners 25 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1263 : OAI.SidorenkoCounterexample.ProofCertificate_1263 := by
  constructor
  exact @certificate_proof_1263 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1264 : Finset.univ.image (pairCorner 26)=pairCorners 26 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1264 : OAI.SidorenkoCounterexample.ProofCertificate_1264 := by
  constructor
  exact @certificate_proof_1264 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1265 : Finset.univ.image (pairCorner 27)=pairCorners 27 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1265 : OAI.SidorenkoCounterexample.ProofCertificate_1265 := by
  constructor
  exact @certificate_proof_1265 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1266 : Finset.univ.image (pairCorner 28)=pairCorners 28 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1266 : OAI.SidorenkoCounterexample.ProofCertificate_1266 := by
  constructor
  exact @certificate_proof_1266 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1267 : Finset.univ.image (pairCorner 29)=pairCorners 29 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1267 : OAI.SidorenkoCounterexample.ProofCertificate_1267 := by
  constructor
  exact @certificate_proof_1267 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1268 : Finset.univ.image (pairCorner 30)=pairCorners 30 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1268 : OAI.SidorenkoCounterexample.ProofCertificate_1268 := by
  constructor
  exact @certificate_proof_1268 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1269 : Finset.univ.image (pairCorner 31)=pairCorners 31 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1269 : OAI.SidorenkoCounterexample.ProofCertificate_1269 := by
  constructor
  exact @certificate_proof_1269 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

lemma certificate_proof_1270 : Finset.univ.image (pairCorner 32)=pairCorners 32 := by
  rw [pairCorners_table]
  decide

private instance certificate_instance_1270 : OAI.SidorenkoCounterexample.ProofCertificate_1270 := by
  constructor
  exact @certificate_proof_1270 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

theorem certificate_proof_1271 (e : Fin 33) : Finset.univ.image (pairCorner e)=pairCorners e := by
  fin_cases e
  · exact pairCorner_image_0
  · exact pairCorner_image_1
  · exact pairCorner_image_2
  · exact pairCorner_image_3
  · exact pairCorner_image_4
  · exact pairCorner_image_5
  · exact pairCorner_image_6
  · exact pairCorner_image_7
  · exact pairCorner_image_8
  · exact pairCorner_image_9
  · exact pairCorner_image_10
  · exact pairCorner_image_11
  · exact pairCorner_image_12
  · exact pairCorner_image_13
  · exact pairCorner_image_14
  · exact pairCorner_image_15
  · exact pairCorner_image_16
  · exact pairCorner_image_17
  · exact pairCorner_image_18
  · exact pairCorner_image_19
  · exact pairCorner_image_20
  · exact pairCorner_image_21
  · exact pairCorner_image_22
  · exact pairCorner_image_23
  · exact pairCorner_image_24
  · exact pairCorner_image_25
  · exact pairCorner_image_26
  · exact pairCorner_image_27
  · exact pairCorner_image_28
  · exact pairCorner_image_29
  · exact pairCorner_image_30
  · exact pairCorner_image_31
  · exact pairCorner_image_32

private instance certificate_instance_1271 : OAI.SidorenkoCounterexample.ProofCertificate_1271 := by
  constructor
  intro q0
  exact @certificate_proof_1271 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0

theorem certificate_proof_1272 (e : Fin 33) : Function.Injective (pairCorner e) := by
  intro a b h
  have h1 := pairFace_injective e (congrArg Prod.fst h)
  rcases a with ⟨a,c⟩; rcases b with ⟨b,d⟩
  dsimp at h1; subst b
  have h2 := congrArg Prod.snd h
  have hn : slotLeft (faceSlot e a)≠slotRight (faceSlot e a) := by
    have hn : ∀ k : Fin 3,slotLeft k≠slotRight k := by decide
    exact hn _
  have : c=d := by fin_cases c <;> fin_cases d <;> simp_all [pairCorner]
  subst d; rfl

private instance certificate_instance_1272 : OAI.SidorenkoCounterexample.ProofCertificate_1272 := by
  constructor
  intro q0
  exact @certificate_proof_1272 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0

theorem certificate_proof_1273 (e : Fin 33) (f : ActCorner → ℝ) :
    (∏ k∈pairCorners e,f k)=∏ b : Fin 2,
      f (pairFace e b,slotLeft (faceSlot e b))*f (pairFace e b,slotRight (faceSlot e b)) := by
  rw [←pairCorner_image,Finset.prod_image (fun _ _ _ _ h => pairCorner_inj e h),Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro b _
  simp [Fin.prod_univ_two,pairCorner]

private instance certificate_instance_1273 : OAI.SidorenkoCounterexample.ProofCertificate_1273 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1273 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section
variable {I L A : Type} [Fintype I] [DecidableEq I] [Fintype L] [Fintype A]
lemma certificate_proof_1274 (p : I → FiniteLaw A) (f : L → I → A → ℝ)
    (g : (I → A) → ℝ) (c : L → ℝ) (hg : ∀ z,g z=∑ l,∏ i,f l i (z i))
    (hc : ∀ l,(∏ i,(p i).mean (f l i))=c l) :
    (FiniteLaw.independent p).mean g=∑ l,c l := by
  calc
    _ = (FiniteLaw.independent p).mean (fun z => ∑ l,∏ i,f l i (z i)) := FiniteLaw.mean_congr _ hg
    _ = ∑ l,(FiniteLaw.independent p).mean (fun z => ∏ i,f l i (z i)) := FiniteLaw.mean_sum _ _
    _ = _ := Finset.sum_congr rfl (fun l _ => (FiniteLaw.independent_mean_product p (f l)).trans (hc l))

private instance certificate_instance_1274 : OAI.SidorenkoCounterexample.ProofCertificate_1274 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_1274 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

lemma certificate_proof_1275 (a b : I → ℝ) :
    uniformMean (fun η : I → Bool => ∏ i,(1+boolSign (η i)*a i)*(1+boolSign (η i)*b i))=
    ∏ i,(1+a i*b i) := by
  rw [uniformMean_pi_product (fun i η => (1+boolSign η*a i)*(1+boolSign η*b i))]
  simp_rw [bool_double_mean]

private instance certificate_instance_1275 : OAI.SidorenkoCounterexample.ProofCertificate_1275 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1275 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4

end
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type} [Fintype K] [DecidableEq K]
lemma certificate_proof_1276 (p : ActCorner → FiniteLaw (Activation K)) (α : Fin 33 → Finset K) :
    (∏ k,(p k).mean (fun z => activationPhi (α (cornerPairL k)) z*activationPhi (α (cornerPairR k)) z))=
    labelProduct (fun k => activationMoment (p k)) α := by rfl

private instance certificate_instance_1276 : OAI.SidorenkoCounterexample.ProofCertificate_1276 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1276 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4

lemma certificate_proof_1277 (p : ActCorner → FiniteLaw (Activation K)) (g : (ActCorner → Activation K) → ℝ)
    (hg : ∀z,g z=∑ α : Fin 33 → Finset K,∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k)) :
    (FiniteLaw.independent p).mean g=∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α := by
  exact FiniteLaw.mean_expansion_product (I := ActCorner) (L := Fin 33 → Finset K) (A := Activation K) p
    (fun α k z => activationPhi (α (cornerPairL k)) z*activationPhi (α (cornerPairR k)) z)
    g (labelProduct (fun k => activationMoment (p k))) hg (activationMoment_product p)

private instance certificate_instance_1277 : OAI.SidorenkoCounterexample.ProofCertificate_1277 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1277 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Expansion
variable {K : Type} [Fintype K] [DecidableEq K]
omit [Fintype K] in
lemma certificate_proof_1278 (α : Fin 33 → Finset K) (z : ActCorner → Activation K) :
    (∏ e,∏ κ∈α e,∏ k∈pairCorners e,activationEntry (z k) κ)=
    ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k) := by
  have he (e : Fin 33) : (∏ κ∈α e,∏ k∈pairCorners e,activationEntry (z k) κ)=
      ∏ k∈pairCorners e,activationPhi (α e) (z k) := by
    rw [Finset.prod_comm]; simp_rw [activationPhi_product]
  simp_rw [he,pairCorners,Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl; intro k _
  have hi (e : Fin 33) : (cornerPairL k=e ∨ cornerPairR k=e) ↔ e∈({cornerPairL k,cornerPairR k} : Finset (Fin 33)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  simp_rw [hi]
  rw [Finset.prod_ite_mem,Finset.univ_inter,Finset.prod_pair (cornerPair_ne k)]

private instance certificate_instance_1278 : OAI.SidorenkoCounterexample.ProofCertificate_1278 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1278 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3

lemma certificate_proof_1279 (z : ActCorner → Activation K) :
    expandedModel z=∑ α : Fin 33 → Finset K,
      ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k) := by
  unfold expandedModel
  rw [Finset.prod_comm,product_one_add_expansion]
  apply Finset.sum_congr rfl; intro α _
  exact labels_incidence_product α z

private instance certificate_instance_1279 : OAI.SidorenkoCounterexample.ProofCertificate_1279 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1279 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3

lemma certificate_proof_1280 (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) :
    (FiniteLaw.independent p).mean expandedModel=1+activeCoefficient (fun k => activationMoment (p k)) := by
  have he : (FiniteLaw.independent p).mean expandedModel=
      ∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α := by
    apply mean_activation_expansion p expandedModel
    intro z
    exact expandedModel_expansion z
  rw [he,allCoefficient_eq p hp]

private instance certificate_instance_1280 : OAI.SidorenkoCounterexample.ProofCertificate_1280 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1280 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4

omit [Fintype K] [DecidableEq K] in
lemma certificate_proof_1281 (z : ActCorner → Activation K) (κ : K) :
    ∀ j k,coordinateSigns z κ j k=1 ∨ coordinateSigns z κ j k= -1 := by
  intro j k; unfold coordinateSigns; split <;> tauto

private instance certificate_instance_1281 : OAI.SidorenkoCounterexample.ProofCertificate_1281 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1281 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4

omit [Fintype K] [DecidableEq K] in
lemma certificate_proof_1282 (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) :
    (coordinateSigns z κ j k : ℝ)=boolSign ((z (j,k)).2 κ) := by
  unfold coordinateSigns boolSign; split <;> simp

private instance certificate_instance_1282 : OAI.SidorenkoCounterexample.ProofCertificate_1282 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1282 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4

omit [Fintype K] in
lemma certificate_proof_1283 (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) (η : Fin 33 → Bool) :
    (if slotLeft k∈coordinateActive z κ j ∧ slotRight k∈coordinateActive z κ j then
      1+(1:ℝ)*boolSign (η (facePair j k))*(coordinateSigns z κ j (slotLeft k):ℝ)*
        (coordinateSigns z κ j (slotRight k):ℝ) else 1)=
      1+boolSign (η (facePair j k))*(activationEntry (z (j,slotLeft k)) κ*activationEntry (z (j,slotRight k)) κ) := by
  simp only [coordinateActive,Finset.mem_filter,Finset.mem_univ,true_and,coordinateSigns_real,one_mul,activationEntry]
  by_cases hl : κ∈(z (j,slotLeft k)).1 <;> by_cases hr : κ∈(z (j,slotRight k)).1 <;>
    simp [hl,hr,mul_assoc]

private instance certificate_instance_1283 : OAI.SidorenkoCounterexample.ProofCertificate_1283 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1283 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6

omit [Fintype K] in
lemma certificate_proof_1284 (z : ActCorner → Activation K) (κ : K) (η : Fin 33 → Bool) :
    boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ) η=
      ∏ e,∏ b : Fin 2,(1+boolSign (η e)*
        (activationEntry (z (pairFace e b,slotLeft (faceSlot e b))) κ*
         activationEntry (z (pairFace e b,slotRight (faceSlot e b))) κ)) := by
  unfold boolConfiguration boolFacePolynomial
  simp_rw [coordinate_factor]
  let f (a : Fin 22 × Fin 3) := 1+boolSign (η (facePair a.1 a.2))*
    (activationEntry (z (a.1,slotLeft a.2)) κ*activationEntry (z (a.1,slotRight a.2)) κ)
  let g (a : Fin 33 × Fin 2) := 1+boolSign (η a.1)*
    (activationEntry (z (pairFace a.1 a.2,slotLeft (faceSlot a.1 a.2))) κ*
     activationEntry (z (pairFace a.1 a.2,slotRight (faceSlot a.1 a.2))) κ)
  change (∏ j,∏ k,f (j,k))=∏ e,∏ b,g (e,b)
  rw [←Fintype.prod_prod_type f,←Fintype.prod_prod_type g]
  exact Fintype.prod_equiv occurrencePairEquiv f g (fun a => by
    change f a=g (facePair a.1 a.2,faceSide a.1 a.2)
    simp only [f,g,faceSide_correct,faceSlot_side])

private instance certificate_instance_1284 : OAI.SidorenkoCounterexample.ProofCertificate_1284 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1284 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4

omit [Fintype K] in
lemma certificate_proof_1285 (z : ActCorner → Activation K) (κ : K) :
    uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ))=
      ∏ e,(1+∏ k∈pairCorners e,activationEntry (z k) κ) := by
  let a (e : Fin 33) := activationEntry (z (pairFace e 0,slotLeft (faceSlot e 0))) κ*
    activationEntry (z (pairFace e 0,slotRight (faceSlot e 0))) κ
  let b (e : Fin 33) := activationEntry (z (pairFace e 1,slotLeft (faceSlot e 1))) κ*
    activationEntry (z (pairFace e 1,slotRight (faceSlot e 1))) κ
  calc
    _ = uniformMean (fun η : Fin 33 → Bool => ∏ e,(1+boolSign (η e)*a e)*(1+boolSign (η e)*b e)) := by
      apply uniformMean_congr; intro η
      rw [coordinate_boolean_product]
      simp only [Fin.prod_univ_two,a,b]
    _ = ∏ e,(1+a e*b e) := uniformMean_double_product a b
    _ = _ := by
      apply Finset.prod_congr rfl; intro e _
      rw [pairCorners_product]
      simp only [Fin.prod_univ_two,a,b]

private instance certificate_instance_1285 : OAI.SidorenkoCounterexample.ProofCertificate_1285 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1285 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3

lemma certificate_proof_1286 (z : ActCorner → Activation K) :
    (∏ κ,uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ)))=expandedModel z := by
  simp_rw [coordinateModel_eq]; rfl

private instance certificate_instance_1286 : OAI.SidorenkoCounterexample.ProofCertificate_1286 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1286 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3

end Expansion
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Fubini
variable {I J K A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]
lemma certificate_proof_1287 (f : K → (I → A) → (J → B) → ℝ) :
    uniformMean (fun x : (I → K → A) × (J → K → B) =>
      ∏ k,f k (fun i => x.1 i k) (fun j => x.2 j k))=
      ∏ k,uniformMean (fun x : (I → A) × (J → B) => f k x.1 x.2) := by
  have h := uniformMean_equiv (coordinateArrayEquiv (I := I) (J := J) (K := K) (A := A) (B := B))
    (fun x => ∏ k,f k (x k).1 (x k).2)
  exact h.trans (uniformMean_pi_product (fun k (x : (I → A) × (J → B)) => f k x.1 x.2))

private instance certificate_instance_1287 : OAI.SidorenkoCounterexample.ProofCertificate_1287 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_1287 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

lemma certificate_proof_1288 (p : FiniteLaw A) (f : A → B → ℝ) :
    uniformMean (fun b => p.mean (fun a => f a b))=p.mean (fun a => uniformMean (f a)) := by
  unfold uniformMean FiniteLaw.mean
  rw [Finset.sum_comm,Finset.sum_div]
  simp_rw [←Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring

private instance certificate_instance_1288 : OAI.SidorenkoCounterexample.ProofCertificate_1288 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1288 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5

lemma certificate_proof_1289 {C : Type} [Fintype C]
    (e : I ≃ J) (p : J → FiniteLaw C) (f : (J → C) → ℝ) :
    (FiniteLaw.independent (fun i => p (e i))).mean (fun x => f (fun j => x (e.symm j)))=
      (FiniteLaw.independent p).mean f := by
  unfold FiniteLaw.mean FiniteLaw.independent
  let E : (I → C) ≃ (J → C) := Equiv.arrowCongr e (Equiv.refl C)
  apply Fintype.sum_equiv E
  intro x
  dsimp [E]
  congr 1
  symm
  exact Fintype.prod_equiv e.symm _ _ (fun j => by simp)

private instance certificate_instance_1289 : OAI.SidorenkoCounterexample.ProofCertificate_1289 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_1289 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

lemma certificate_proof_1290 (p : I → FiniteLaw A) (q : I → FiniteLaw B) (f : (I → A × B) → ℝ) :
    (FiniteLaw.independent (fun i => (p i).prod (q i))).mean f=
      (FiniteLaw.independent p).mean (fun x => (FiniteLaw.independent q).mean (fun y => f (fun i => (x i,y i)))) := by
  unfold FiniteLaw.mean FiniteLaw.independent FiniteLaw.prod
  simp_rw [Finset.mul_sum,←mul_assoc,←Finset.prod_mul_distrib]
  rw [←Fintype.sum_prod_type (fun xy : (I → A) × (I → B) =>
    (∏ i,(p i).weight (xy.1 i)*(q i).weight (xy.2 i))*f (fun i => (xy.1 i,xy.2 i)))]
  let e : (I → A × B) ≃ ((I → A) × (I → B)) := {
    toFun x := (fun i => (x i).1,fun i => (x i).2)
    invFun x i := (x.1 i,x.2 i)
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => by rfl)

private instance certificate_instance_1290 : OAI.SidorenkoCounterexample.ProofCertificate_1290 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1290 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end Fubini
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
theorem certificate_proof_1291 (j : Fin 22) (k : Fin 3) : faceVertex j k∈faces j := by
  rw [faceVertex_correct]
  fin_cases k <;> simp

private instance certificate_instance_1291 : OAI.SidorenkoCounterexample.ProofCertificate_1291 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1291 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1

theorem certificate_proof_1292 (j : Fin 22) (i : Fin 13) (hi : i∈faces j) : ∃ k,faceVertex j k=i := by
  rw [faceVertex_correct] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with h|h|h
  · exact ⟨0,h.symm⟩
  · exact ⟨1,h.symm⟩
  · exact ⟨2,h.symm⟩

private instance certificate_instance_1292 : OAI.SidorenkoCounterexample.ProofCertificate_1292 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1292 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Filter
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_1235 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1236 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1237 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1238 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1239 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1240 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1241 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1242 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1243 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1244 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1245 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1246 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1247 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1248 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1249 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1250 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1251 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1252 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1253 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1254 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1255 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1256 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1257 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1258 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1259 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1260 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1261 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1262 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1263 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1264 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1265 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1266 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1267 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1268 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1269 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1270 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1271 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1272 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1273 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1274 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1275 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1276 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1277 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1278 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1279 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1280 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1281 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1282 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1283 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1284 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1285 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1286 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1287 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1288 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1289 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1290 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1291 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1292 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

