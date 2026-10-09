-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_37
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:46:25.542979+00:00
-- url     : https://prove2.me/submissions/8771ac11-3ab4-451c-bb29-e86e01e43558

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0373]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0374]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0457]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0605]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0643]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0647]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0655]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0898]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0899]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0919]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0958]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0972]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0973]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0975]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0999]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_1000]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_1001]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_1008]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_1012]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_1014]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_1015]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_1016]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_1018]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_1020]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_1022]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_1025]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_1029]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_1214]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_1215]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_1220]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_1229]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_1280]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_1281]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_1286]
  [p41 : OAI.SidorenkoCounterexample.ProofCertificate_1287]
  [p42 : OAI.SidorenkoCounterexample.ProofCertificate_1288]
  [p43 : OAI.SidorenkoCounterexample.ProofCertificate_1290]
  [p44 : OAI.SidorenkoCounterexample.ProofCertificate_1292]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44

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
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section
variable {I L A : Type} [Fintype I] [DecidableEq I] [Fintype L] [Fintype A]
end
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
section Expansion
variable {K : Type} [Fintype K] [DecidableEq K]
end Expansion
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Fubini
variable {I J K A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]
end Fubini
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
theorem certificate_proof_1293 {M : Type} [CommMonoid M] (B : Finset (Fin 13 × Fin 22))
    (hB : B⊆corners) (f : Fin 13 × Fin 22 → M) :
    (∏ c∈B,f c)=∏ j,∏ k∈faceActive B j,f (faceVertex j k,j) := by
  rw [Finset.prod_sigma' Finset.univ (faceActive B) (fun j k => f (faceVertex j k,j))]
  symm
  apply Finset.prod_bij (fun a _ => (faceVertex a.1 a.2,a.1))
  · intro a ha
    have h := (Finset.mem_sigma.mp ha).2
    exact (Finset.mem_filter.mp h).2
  · intro a ha b hb he
    have h1 : a.1=b.1 := congrArg Prod.snd he
    rcases a with ⟨j,k⟩; rcases b with ⟨l,m⟩
    dsimp at h1; subst l
    have h2 := faceVertex_injective j (congrArg Prod.fst he)
    change k=m at h2
    subst m; rfl
  · intro b hb
    have hi : b.1∈faces b.2 := (Finset.mem_filter.mp (hB hb)).2
    obtain ⟨k,hk⟩ := faceVertex_surj b.2 b.1 hi
    refine ⟨⟨b.2,k⟩,?_,?_⟩
    · simp only [Finset.mem_sigma,Finset.mem_univ,true_and,faceActive,Finset.mem_filter]
      simpa only [hk,true_and,Prod.eta] using hb
    · simp only [hk,Prod.eta]
  · intros; rfl

private instance certificate_instance_1293 : OAI.SidorenkoCounterexample.ProofCertificate_1293 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1293 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

theorem certificate_proof_1294 (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ)
    (hξ : ∀ c∈B,ξ c=1 ∨ ξ c= -1) : ∀ j k,faceSigns B ξ j k=1 ∨ faceSigns B ξ j k= -1 := by
  intro j k
  unfold faceSigns
  split_ifs with h
  · exact hξ _ h
  · exact Or.inl rfl

private instance certificate_instance_1294 : OAI.SidorenkoCounterexample.ProofCertificate_1294 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1294 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

theorem certificate_proof_1295 (r : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (hB : B⊆corners) (ξ : Fin 13 × Fin 22 → ℤ) :
    layerCorrelation (2*r) q B ξ=uniformMean (configurationProduct (K := ZMod q.val) r (faceActive B) (faceSigns B ξ)) := by
  have hm : 2*r/2=r := by omega
  unfold layerCorrelation
  rw [uniformMean_prod]
  apply uniformMean_congr; intro X
  have he (Y : Fin 22 → SymMatrix (ZMod q.val) (2*r)) :
      (∏ c∈B, rankKernel (ZMod q.val) (2*r) (2*r/2) (ξ c) (X c.1-Y c.2))=
      ∏ j,∏ k∈faceActive B j,rankKernel (ZMod q.val) (2*r) r (faceSigns B ξ j k) (X (faceVertex j k)-Y j) := by
    rw [corners_product B hB]
    apply Finset.prod_congr rfl; intro j _
    apply Finset.prod_congr rfl; intro k hk
    have hk := (Finset.mem_filter.mp hk).2
    simp only [faceSigns,hk,ite_true,hm]
  simp_rw [he]
  exact uniformMean_pi_product (fun j y => ∏ k ∈ faceActive B j,
    rankKernel (ZMod q.val) (2*r) r (faceSigns B ξ j k) (X (faceVertex j k)-y))

private instance certificate_instance_1295 : OAI.SidorenkoCounterexample.ProofCertificate_1295 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1295 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

theorem certificate_proof_1296 : ∀ (j : Fin 22) (e : Fin 33),
    pairVertices e⊆faces j ↔ ∃ k,facePair j k=e := by decide

private instance certificate_instance_1296 : OAI.SidorenkoCounterexample.ProofCertificate_1296 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1296 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1

theorem certificate_proof_1297 (j : Fin 22) (f : Fin 33 → ℝ)
    (hf : ∀ e,¬pairVertices e⊆faces j → f e=1) : (∏ e,f e)=∏ k,f (facePair j k) := by
  let S := Finset.univ.image (facePair j)
  have he : (∏ e,f e)=∏ e∈S,f e := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    apply hf e
    rw [pair_sub_face_iff]
    simpa only [S,Finset.mem_image,Finset.mem_univ,true_and] using he
  rw [he]
  exact Finset.prod_image (fun _ _ _ _ h => facePair_injective j h)

private instance certificate_instance_1297 : OAI.SidorenkoCounterexample.ProofCertificate_1297 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1297 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2

theorem certificate_proof_1298 (c : ℝ) (B : Finset (Fin 13 × Fin 22))
    (ξ : Fin 13 × Fin 22 → ℤ) (η : Fin 33 → Bool) (j : Fin 22) :
    (∏ e : ModelPair, if e.val⊆faces j ∧ (∀ i∈e.val,(i,j)∈B) then
      1+c*boolSign (η (pairModelEquiv.symm e))*∏ i∈e.val,(ξ (i,j):ℝ) else 1)=
    boolFacePolynomial c (faceActive B j) (faceSigns B ξ j) j η := by
  rw [←Equiv.prod_comp pairModelEquiv]
  simp only [Equiv.symm_apply_apply]
  change (∏ e : Fin 33,if pairVertices e⊆faces j ∧ (∀ i∈pairVertices e,(i,j)∈B) then
      1+c*boolSign (η e)*∏ i∈pairVertices e,(ξ (i,j):ℝ) else 1)=_
  rw [product_facePair j _ (fun e he => if_neg (by tauto))]
  apply Finset.prod_congr rfl; intro k _
  have hf : pairVertices (facePair j k)⊆faces j := (pair_sub_face_iff j _).mpr ⟨k,rfl⟩
  have hp : pairVertices (facePair j k)={faceVertex j (slotLeft k),faceVertex j (slotRight k)} := by
    rw [pair_endpoints,(facePair_endpoints j k).1,(facePair_endpoints j k).2]
  have hne : faceVertex j (slotLeft k)≠faceVertex j (slotRight k) := by
    rw [←(facePair_endpoints j k).1,←(facePair_endpoints j k).2]
    exact pair_endpoints_ne _
  simp only [hf,true_and]
  simp only [hp,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,
    Finset.prod_pair hne,faceActive,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases h : (faceVertex j (slotLeft k),j)∈B ∧ (faceVertex j (slotRight k),j)∈B
  · simp only [faceSigns,h.1,h.2,and_self,ite_true]; ring
  · simp only [h,ite_false]

private instance certificate_instance_1298 : OAI.SidorenkoCounterexample.ProofCertificate_1298 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4
  exact @certificate_proof_1298 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

theorem certificate_proof_1299 (r : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ) :
    signModelCorrelation (2*r) q B ξ=uniformMean
      (boolConfiguration (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) (faceActive B) (faceSigns B ξ)) := by
  unfold signModelCorrelation
  simp only [show 2*r/2=r by omega]
  rw [←uniformMean_equiv pairBoolEquiv]
  apply uniformMean_congr; intro η
  change (∏ j, ∏ e : ModelPair, if e.val⊆faces j ∧ (∀ i∈e.val,(i,j)∈B) then
    1+(quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r):ℝ)*boolSign (η (pairModelEquiv.symm e))*
      ∏ i∈e.val,(ξ (i,j):ℝ) else 1)=_
  apply Finset.prod_congr rfl; intro j _
  exact modelFace_polynomial _ B ξ η j

private instance certificate_instance_1299 : OAI.SidorenkoCounterexample.ProofCertificate_1299 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1299 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
theorem certificate_proof_1300 (r : ℕ) (hbig : 12≤2*r) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (c : ℝ) : Tendsto
    (boolTestError r T ξ c) primeInfinity (nhds 0) := by
  unfold boolTestError
  simpa only [sub_self] using
    (pairBool_test_tendsto (2*r) (even_two_mul r) hbig (boolConfiguration c T ξ)).sub_const
      (uniformMean (boolConfiguration c T ξ))

private instance certificate_instance_1300 : OAI.SidorenkoCounterexample.ProofCertificate_1300 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1300 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

theorem certificate_proof_1301 (r : ℕ) (hbig : 12≤2*r) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : Tendsto
    (fun q : OddPrime => boolTestError r T ξ
      (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) q) primeInfinity (nhds 0) := by
  have ht := ((boolTestError_tendsto r hbig T ξ 1).abs).add ((boolTestError_tendsto r hbig T ξ (-1)).abs)
  simp only [abs_zero,add_zero] at ht
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  rcases quadraticChar_dichotomy (F := ZMod q.val) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)) with h|h
  · simp only [h,Int.cast_one]; exact le_add_of_nonneg_right (abs_nonneg _)
  · simp only [h,Int.cast_neg,Int.cast_one]; exact le_add_of_nonneg_left (abs_nonneg _)

private instance certificate_instance_1301 : OAI.SidorenkoCounterexample.ProofCertificate_1301 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1301 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3

theorem certificate_proof_1302 (r : ℕ) (hlarge : singularTailThreshold≤2*r)
    (B : Finset (Fin 13 × Fin 22)) (hB : B⊆corners) (ξ : Fin 13 × Fin 22 → ℤ)
    (hξ : ∀ c∈B,ξ c=1 ∨ ξ c= -1) : Tendsto
      (fun q : OddPrime => layerCorrelation (2*r) q B ξ-signModelCorrelation (2*r) q B ξ)
      primeInfinity (nhds 0) := by
  have hb : 12≤2*r := by have := singularTailThreshold_large; omega
  have h1 := configuration_bool_tendsto r (faceActive B) (faceSigns B ξ) (faceSigns_good B ξ hξ) hlarge
  have h2 := varyingBoolTestError_tendsto r hb (faceActive B) (faceSigns B ξ)
  have ht := h1.add h2
  simp only [add_zero] at ht
  convert ht using 1
  funext q
  rw [layerCorrelation_configuration r q B hB ξ,signModelCorrelation_configuration]
  unfold boolTestError
  ring

private instance certificate_instance_1302 : OAI.SidorenkoCounterexample.ProofCertificate_1302 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1302 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5

theorem certificate_proof_1303 : RankLayerLimit := by
  refine ⟨singularTailThreshold,?_,?_⟩
  · have := singularTailThreshold_large; omega
  intro D hD he B hB ξ hξ
  obtain ⟨r,hr⟩ := he
  have h : D=2*r := by omega
  rw [h] at hD ⊢
  exact rankLayerConvergence r hD B hB ξ hξ

private instance certificate_instance_1303 : OAI.SidorenkoCounterexample.ProofCertificate_1303 := by
  constructor
  exact @certificate_proof_1303 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Filter
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section MatrixActivation
variable {F K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
lemma certificate_proof_1304 (r : ℕ) (z : ActCorner → Activation K)
    (x : Fin 13 → K → SymMatrix F (2*r)) (y : Fin 22 → K → SymMatrix F (2*r)) :
    matrixSampleProduct r z x y=∏ κ,∏ j,∏ k∈coordinateActive z κ j,
      rankKernel F (2*r) r (coordinateSigns z κ j k) (x (faceVertex j k) κ-y j κ) := by
  unfold matrixSampleProduct sampleMatrixKernel
  have he (k : ActCorner) :
      (∏ κ∈(z k).1,rankKernel F (2*r) r (if (z k).2 κ then 1 else -1) (x (cornerPoint k) κ-y k.1 κ))=
      ∏ κ,if κ∈(z k).1 then rankKernel F (2*r) r (if (z k).2 κ then 1 else -1) (x (cornerPoint k) κ-y k.1 κ) else 1 := by
    simp only [Finset.prod_ite_mem,Finset.univ_inter]
  simp_rw [he]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl; intro κ _
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro j _
  rw [coordinateActive,Finset.prod_filter]
  rfl

private instance certificate_instance_1304 : OAI.SidorenkoCounterexample.ProofCertificate_1304 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_1304 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

lemma certificate_proof_1305 (r : ℕ) (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ) :
    uniformMean (fun xy : (Fin 13 → SymMatrix F (2*r)) × (Fin 22 → SymMatrix F (2*r)) =>
      ∏ j,∏ k∈T j,rankKernel F (2*r) r (ξ j k) (xy.1 (faceVertex j k)-xy.2 j))=
      uniformMean (configurationProduct (K := F) r T ξ) := by
  rw [uniformMean_prod]
  apply uniformMean_congr; intro X
  rw [uniformMean_pi_product (fun j Y => ∏ k∈T j,rankKernel F (2*r) r (ξ j k) (X (faceVertex j k)-Y))]
  rfl

private instance certificate_instance_1305 : OAI.SidorenkoCounterexample.ProofCertificate_1305 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1305 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6

lemma certificate_proof_1306 (r : ℕ) (z : ActCorner → Activation K) :
    uniformMean (fun xy : (Fin 13 → K → SymMatrix F (2*r)) × (Fin 22 → K → SymMatrix F (2*r)) =>
      matrixSampleProduct r z xy.1 xy.2)=
      ∏ κ,uniformMean (configurationProduct (K := F) r (coordinateActive z κ) (coordinateSigns z κ)) := by
  simp_rw [matrixSampleProduct_coordinates]
  rw [uniformMean_coordinate_factor (fun κ X Y => ∏ j,∏ k∈coordinateActive z κ j,
    rankKernel F (2*r) r (coordinateSigns z κ j k) (X (faceVertex j k)-Y j))]
  simp_rw [coordinateMatrixIntegral]

private instance certificate_instance_1306 : OAI.SidorenkoCounterexample.ProofCertificate_1306 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_1306 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8

lemma certificate_proof_1307 (r : ℕ) (p : ActCorner → FiniteLaw (Activation K)) :
    conditionalMatrixMoment (F := F) r p=(FiniteLaw.independent p).mean (fun z =>
      ∏ κ,uniformMean (configurationProduct (K := F) r (coordinateActive z κ) (coordinateSigns z κ))) := by
  unfold conditionalMatrixMoment activationMatrixKernel
  simp_rw [←FiniteLaw.independent_mean_product]
  rw [uniformMean_law_swap]
  apply FiniteLaw.mean_congr; intro z
  exact matrixSampleProduct_mean r z

private instance certificate_instance_1307 : OAI.SidorenkoCounterexample.ProofCertificate_1307 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_1307 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8

omit [Fintype K] [DecidableEq K] in
lemma certificate_proof_1308 (r : ℕ) (z : Activation K) (x y : K → SymMatrix F (2*r)) :
    0≤ sampleMatrixKernel r z x y := Finset.prod_nonneg (fun _ _ => rankKernel_nonneg ..)

private instance certificate_instance_1308 : OAI.SidorenkoCounterexample.ProofCertificate_1308 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_1308 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8

lemma certificate_proof_1309 (r : ℕ) (p : FiniteLaw (Activation K)) (x y : K → SymMatrix F (2*r)) :
    0≤activationMatrixKernel r p x y := p.mean_nonneg (fun z => sampleMatrixKernel_nonneg r z x y)

private instance certificate_instance_1309 : OAI.SidorenkoCounterexample.ProofCertificate_1309 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_1309 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end MatrixActivation
lemma certificate_proof_1310 (r : ℕ) (hl : singularTailThreshold≤2*(2*r))
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j k,ξ j k=1 ∨ ξ j k= -1) : Tendsto
    (fun q : OddPrime => uniformMean (configurationProduct (K := ZMod q.val) (2*r) T ξ))
    primeInfinity (nhds (uniformMean (boolConfiguration 1 T ξ))) := by
  have hch (q : OddPrime) : (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^(2*r)):ℝ)=1 := by
    rw [Even.neg_one_pow (even_two_mul r)]; simp
  have h₁ := configuration_bool_tendsto (2*r) T ξ hξ hl
  have h₂ := boolTestError_tendsto (2*r) (by have := singularTailThreshold_large; omega) T ξ 1
  simp_rw [hch] at h₁
  have h := (h₁.add h₂).add_const (uniformMean (boolConfiguration 1 T ξ))
  simp only [zero_add,add_zero] at h
  convert h using 1
  funext q
  unfold boolTestError
  ring

private instance certificate_instance_1310 : OAI.SidorenkoCounterexample.ProofCertificate_1310 := by
  constructor
  intro c0 q0 q1 q2 q3 q4
  exact @certificate_proof_1310 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

lemma certificate_proof_1311 {K : Type} [Fintype K] [DecidableEq K]
    (r : ℕ) (hl : singularTailThreshold≤2*(2*r)) (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) : Tendsto
    (fun q : OddPrime => conditionalMatrixMoment (F := ZMod q.val) (2*r) p) primeInfinity
    (nhds (1+activeCoefficient (fun k => activationMoment (p k)))) := by
  have h (z : ActCorner → Activation K) := tendsto_finsetProd Finset.univ (fun κ _ =>
    configuration_even_rank_limit r hl (coordinateActive z κ) (coordinateSigns z κ) (coordinateSigns_good z κ))
  have ht := FiniteLaw.mean_tendsto (FiniteLaw.independent p) _ _ h
  simp only [coordinateModels_product,expandedModel_mean p hp] at ht
  simpa only [conditionalMatrixMoment_law] using ht

private instance certificate_instance_1311 : OAI.SidorenkoCounterexample.ProofCertificate_1311 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1311 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Types
variable {K : Type} [Fintype K] [DecidableEq K]
omit [Fintype K] in
lemma certificate_proof_1312 (α : Finset K) : activationPhi α (∅,fun _ => false)=if α=∅ then 1 else 0 := by
  by_cases he : α=∅
  · subst α; simp
  · simp [activationPhi,Finset.subset_empty,he]

private instance certificate_instance_1312 : OAI.SidorenkoCounterexample.ProofCertificate_1312 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1312 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2

lemma certificate_proof_1313 (α : Finset K) (hα : α≠∅) : inactiveLaw.mean (activationPhi α)=0 := by
  simp only [inactiveLaw,FiniteLaw.mean_dirac,inactivePhi,if_neg hα]

private instance certificate_instance_1313 : OAI.SidorenkoCounterexample.ProofCertificate_1313 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1313 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

lemma certificate_proof_1314 (α β : Finset K) : activationMoment inactiveLaw α β=if α=∅ ∧ β=∅ then 1 else 0 := by
  simp only [activationMoment,inactiveLaw,FiniteLaw.mean_dirac,inactivePhi]
  by_cases hα : α=∅ <;> by_cases hβ : β=∅ <;> simp [hα,hβ]

private instance certificate_instance_1314 : OAI.SidorenkoCounterexample.ProofCertificate_1314 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1314 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

lemma certificate_proof_1315 (p : FiniteLaw (Activation K)) (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0)
    (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) (α : Finset K) (hα : α≠∅) :
    (thinnedLaw p lam hlam hlam1).mean (activationPhi α)=0 := by
  rw [thinnedLaw,FiniteLaw.mean_mixture,hp α hα,inactiveLaw_zero α hα]; ring

private instance certificate_instance_1315 : OAI.SidorenkoCounterexample.ProofCertificate_1315 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1315 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

lemma certificate_proof_1316 (p : FiniteLaw (Activation K)) (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1)
    (α β : Finset K) (hα : α≠∅) :
    activationMoment (thinnedLaw p lam hlam hlam1) α β=lam*activationMoment p α β := by
  unfold activationMoment thinnedLaw
  rw [FiniteLaw.mean_mixture]
  have hz : inactiveLaw.mean (fun z : Activation K => activationPhi α z*activationPhi β z)=0 := by
    change activationMoment inactiveLaw α β=0
    simp only [inactiveLaw_moment,hα,false_and,ite_false]
  rw [hz]; ring

private instance certificate_instance_1316 : OAI.SidorenkoCounterexample.ProofCertificate_1316 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1316 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

lemma certificate_proof_1317 (p : ActCorner → FiniteLaw (Activation K)) (lam : ActCorner → ℝ)
    (hlam : ∀ k,0≤lam k) (hlam1 : ∀ k,lam k≤1) :
    activeCoefficient (fun k => activationMoment (thinnedLaw (p k) (lam k) (hlam k) (hlam1 k)))=
      (∏ k,lam k)*activeCoefficient (fun k => activationMoment (p k)) := by
  unfold activeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro α hα
  have ha := (mem_nonemptyLabels α).mp hα
  unfold labelProduct
  simp_rw [thinnedLaw_active _ _ _ _ _ _ (ha _),Finset.prod_mul_distrib]

private instance certificate_instance_1317 : OAI.SidorenkoCounterexample.ProofCertificate_1317 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1317 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6

lemma certificate_proof_1318 (p : ActCorner → FiniteLaw (Activation K)) (k : ActCorner)
    (hk : p k=inactiveLaw) : activeCoefficient (fun k => activationMoment (p k))=0 := by
  unfold activeCoefficient
  apply Finset.sum_eq_zero; intro α hα
  have ha := (mem_nonemptyLabels α).mp hα
  unfold labelProduct
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  dsimp only
  rw [hk,inactiveLaw_moment]
  simp only [ha,false_and,ite_false]

private instance certificate_instance_1318 : OAI.SidorenkoCounterexample.ProofCertificate_1318 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1318 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5

end Types
lemma certificate_proof_1319 (k : ActCorner) : basePairLaw (cornerPoint k) k.1=cornerLaw k := by
  obtain ⟨j,k⟩ := k
  have hinj := faceVertex_injective j
  have h01 : faceVertex j 1≠faceVertex j 0 := fun h => (by decide : (1:Fin 3)≠0) (hinj h)
  have h20 : faceVertex j 2≠faceVertex j 0 := fun h => (by decide : (2:Fin 3)≠0) (hinj h)
  have h21 : faceVertex j 2≠faceVertex j 1 := fun h => (by decide : (2:Fin 3)≠1) (hinj h)
  fin_cases k <;> simp [basePairLaw,cornerPoint,h01,h20,h21]

private instance certificate_instance_1319 : OAI.SidorenkoCounterexample.ProofCertificate_1319 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 q0
  exact @certificate_proof_1319 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0

lemma certificate_proof_1320 (a : Fin 13) (b : Fin 22) (α : Finset ActCorner) (hα : α≠∅) :
    (basePairLaw a b).mean (activationPhi α)=0 := by
  unfold basePairLaw; split
  · exact cornerLaw_zero _ α hα
  · split
    · exact cornerLaw_zero _ α hα
    · split
      · exact cornerLaw_zero _ α hα
      · exact inactiveLaw_zero α hα

private instance certificate_instance_1320 : OAI.SidorenkoCounterexample.ProofCertificate_1320 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 q0 q1 q2 q3
  exact @certificate_proof_1320 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3

lemma certificate_proof_1321 : activeCoefficient (fun k => activationMoment (basePairLaw (cornerPoint k) k.1))= -(1/4:ℝ)^66 := by
  simp only [basePairLaw_corner]
  exact identity_activeCoefficient

private instance certificate_instance_1321 : OAI.SidorenkoCounterexample.ProofCertificate_1321 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6
  exact @certificate_proof_1321 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44

lemma certificate_proof_1322 : Function.Surjective cornerPoint := by decide

private instance certificate_instance_1322 : OAI.SidorenkoCounterexample.ProofCertificate_1322 := by
  constructor
  exact @certificate_proof_1322 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Typed
variable {A B K : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
omit [Fintype A] [Fintype B] in
lemma certificate_proof_1323 (p : A → B → FiniteLaw (Activation K)) (lam : A → B → ℝ)
    (h0 : ∀ a b,0≤lam a b) (h1 : ∀ a b,lam a b≤1) (a : Fin 13 → A) (b : Fin 22 → B) :
    typedCoefficient (fun a b => thinnedLaw (p a b) (lam a b) (h0 a b) (h1 a b)) a b=
      (∏ k : ActCorner,lam (a (cornerPoint k)) (b k.1))*typedCoefficient p a b :=
  activeCoefficient_scaling _ _ _ _

private instance certificate_instance_1323 : OAI.SidorenkoCounterexample.ProofCertificate_1323 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_1323 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

omit [Fintype A] [Fintype B] in
lemma certificate_proof_1324 (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
    (b : Fin 22 → B) (i : Fin 13) (hi : ∀ j,p (a i) j=inactiveLaw) : typedCoefficient p a b=0 := by
  obtain ⟨k,hk⟩ := cornerPoint_surjective i
  exact activeCoefficient_inactive _ k (by rw [hk]; exact hi _)

private instance certificate_instance_1324 : OAI.SidorenkoCounterexample.ProofCertificate_1324 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1324 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [Fintype A] [Fintype B] in
lemma certificate_proof_1325 (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
    (b : Fin 22 → B) (j : Fin 22) (hj : ∀ i,p i (b j)=inactiveLaw) : typedCoefficient p a b=0 :=
  activeCoefficient_inactive _ (j,0) (hj _)

private instance certificate_instance_1325 : OAI.SidorenkoCounterexample.ProofCertificate_1325 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1325 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end Typed
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Kernel
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
lemma certificate_proof_1326 (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ)
    (hW : ∀ x y,0≤W x y) : 0≤bipartiteMoment π ν W :=
  FiniteLaw.mean_nonneg _ (fun _ => FiniteLaw.mean_nonneg _ (fun _ => Finset.prod_nonneg (fun _ _ => hW _ _)))

private instance certificate_instance_1326 : OAI.SidorenkoCounterexample.ProofCertificate_1326 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_1326 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7

lemma certificate_proof_1327 (π : FiniteLaw X) (ν : FiniteLaw Y) {W Z : X → Y → ℝ}
    (h : ∀ x y,W x y=Z x y) : bipartiteMoment π ν W=bipartiteMoment π ν Z := by
  unfold bipartiteMoment
  apply FiniteLaw.mean_congr; intro x
  apply FiniteLaw.mean_congr; intro y
  exact Finset.prod_congr rfl fun k _ => h _ _

private instance certificate_instance_1327 : OAI.SidorenkoCounterexample.ProofCertificate_1327 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_1327 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8

lemma certificate_proof_1328 (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
    (W : A × X → B × Y → ℝ) :
    bipartiteMoment (π.prod σ) (ν.prod τ) W=
      (typeMapLaw π ν).mean (fun ab => (FiniteLaw.independent (fun _ : Fin 13 => σ)).mean (fun x =>
        (FiniteLaw.independent (fun _ : Fin 22 => τ)).mean (fun y =>
          ∏ k : ActCorner,W (ab.1 (cornerPoint k),x (cornerPoint k)) (ab.2 k.1,y k.1)))) := by
  unfold bipartiteMoment typeMapLaw
  rw [FiniteLaw.mean_prod,independent_mean_prod]
  apply FiniteLaw.mean_congr; intro a
  simp_rw [independent_mean_prod]
  exact FiniteLaw.mean_swap _ _ _

private instance certificate_instance_1328 : OAI.SidorenkoCounterexample.ProofCertificate_1328 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_1328 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

lemma certificate_proof_1329 (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
    (W : A × X → B × Y → ℝ) : kernelMean (π.prod σ) (ν.prod τ) W=
      π.mean (fun a => ν.mean (fun b => σ.mean (fun x => τ.mean (fun y => W (a,x) (b,y))))) := by
  unfold kernelMean
  rw [FiniteLaw.mean_prod]
  apply FiniteLaw.mean_congr; intro a
  simp_rw [FiniteLaw.mean_prod]
  exact FiniteLaw.mean_swap _ _ _

private instance certificate_instance_1329 : OAI.SidorenkoCounterexample.ProofCertificate_1329 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_1329 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Kernel
namespace FiniteLaw
lemma certificate_proof_1330 {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (f : (I → A) → ℝ) : (independent (fun _ : I => (uniform : FiniteLaw A))).mean f=uniformMean f := by
  unfold mean independent uniform uniformMean
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,←inv_pow,←Finset.mul_sum,div_eq_mul_inv]
  ring

private instance certificate_instance_1330 : OAI.SidorenkoCounterexample.ProofCertificate_1330 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1330 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6

end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section MatrixMean
variable {F K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
lemma certificate_proof_1331 {A : Type} [AddGroup A] [Fintype A] (y : A) (f : A → ℝ) :
    uniformMean (fun x => f (x-y))=uniformMean f := uniformMean_equiv (Equiv.subRight y) f

private instance certificate_instance_1331 : OAI.SidorenkoCounterexample.ProofCertificate_1331 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1331 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4

lemma certificate_proof_1332 (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
    (z : Activation K) (y : K → SymMatrix F (2*r)) :
    uniformMean (fun x => sampleMatrixKernel r z x y)=1 := by
  have he (x : K → SymMatrix F (2*r)) : sampleMatrixKernel r z x y=
      ∏ κ,if κ∈z.1 then rankKernel F (2*r) r (if z.2 κ then 1 else -1) (x κ-y κ) else 1 := by
    simp only [sampleMatrixKernel,Finset.prod_ite_mem,Finset.univ_inter]
  simp only [he]
  rw [uniformMean_pi_product (fun κ x => if κ∈z.1 then rankKernel F (2*r) r (if z.2 κ then 1 else -1) (x-y κ) else 1)]
  have hm (κ : K) : uniformMean (fun x : SymMatrix F (2*r) =>
      if κ∈z.1 then rankKernel F (2*r) r (if z.2 κ then 1 else -1) (x-y κ) else 1)=1 := by
    by_cases hκ : κ∈z.1
    · simp only [hκ,ite_true,uniformMean_sub_right]
      exact uniformMean_rankKernel (2*r) r hr (by omega) hF (by split <;> simp)
    · simp only [hκ,ite_false,uniformMean_const]
  simp only [hm,Finset.prod_const_one]

private instance certificate_instance_1332 : OAI.SidorenkoCounterexample.ProofCertificate_1332 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_1332 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

lemma certificate_proof_1333 (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
    (p : FiniteLaw (Activation K)) (y : K → SymMatrix F (2*r)) :
    uniformMean (fun x => activationMatrixKernel r p x y)=1 := by
  unfold activationMatrixKernel
  rw [uniformMean_law_swap]
  simp only [sampleMatrixKernel_mean r hr hF,FiniteLaw.mean_const]

private instance certificate_instance_1333 : OAI.SidorenkoCounterexample.ProofCertificate_1333 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_1333 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

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
end TypedMatrix
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_1293 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1294 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1295 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1296 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1297 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1298 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1299 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1300 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1301 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1302 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1303 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1304 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1305 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1306 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1307 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1308 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1309 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1310 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1311 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1312 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1313 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1314 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1315 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1316 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1317 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1318 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1319 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1320 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1321 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1322 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1323 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1324 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1325 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1326 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1327 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1328 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1329 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1330 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1331 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1332 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1333 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

