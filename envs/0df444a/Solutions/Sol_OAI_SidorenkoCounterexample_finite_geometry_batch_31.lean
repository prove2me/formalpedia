-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_31
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:37:02.006435+00:00
-- url     : https://prove2.me/submissions/01290fab-0835-4dc0-8882-8b9afef79e5f

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0013]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0034]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0198]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0372]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0591]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0598]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0604]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0605]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0614]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0615]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0643]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0655]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0661]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0664]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0791]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0813]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0814]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0815]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0816]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0824]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0827]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0856]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0857]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0859]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0860]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0890]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0898]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0920]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0927]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_0929]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_0930]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_0931]
  [p41 : OAI.SidorenkoCounterexample.ProofCertificate_0932]
  [p42 : OAI.SidorenkoCounterexample.ProofCertificate_0933]
  [p43 : OAI.SidorenkoCounterexample.ProofCertificate_0934]
  [p44 : OAI.SidorenkoCounterexample.ProofCertificate_0935]
  [p45 : OAI.SidorenkoCounterexample.ProofCertificate_0938]
  [p46 : OAI.SidorenkoCounterexample.ProofCertificate_0940]
  [p47 : OAI.SidorenkoCounterexample.ProofCertificate_0941]
  [p48 : OAI.SidorenkoCounterexample.ProofCertificate_0942]
  [p49 : OAI.SidorenkoCounterexample.ProofCertificate_0943]
  [p50 : OAI.SidorenkoCounterexample.ProofCertificate_0944]
  [p51 : OAI.SidorenkoCounterexample.ProofCertificate_0946]
  [p52 : OAI.SidorenkoCounterexample.ProofCertificate_0950]
  [p53 : OAI.SidorenkoCounterexample.ProofCertificate_0952]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53

namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Mean
variable {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
end Mean
section Norm
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Norm
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Face
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Face
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Boolean
variable {I : Type} [Fintype I] [DecidableEq I]
omit [DecidableEq I] in
theorem certificate_proof_0953 (η ε : I → Bool) :
    (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
      ∑ F : Finset I, boolMonomial F η * boolMonomial F ε := by
  rw [bool_indicator_product,Finset.prod_one_add]
  simp only [Finset.powerset_univ,Finset.prod_mul_distrib,boolMonomial]

private instance certificate_instance_0953 : OAI.SidorenkoCounterexample.ProofCertificate_0953 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0953 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3

variable {A : Type} [Fintype A]
omit [DecidableEq I] in
theorem certificate_proof_0954 (T : A → I → Bool) (ε : I → Bool) :
    uniformMean (fun a => if T a=ε then 1 else 0)=
      (2^Fintype.card I : ℝ)⁻¹ * ∑ F : Finset I,
        (uniformMean fun a => boolMonomial F (T a))*boolMonomial F ε := by
  simp_rw [bool_indicator_expansion]
  rw [uniformMean_mul,uniformMean_sum]
  simp_rw [uniformMean_mul_right]

private instance certificate_instance_0954 : OAI.SidorenkoCounterexample.ProofCertificate_0954 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0954 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0955 (T : A → I → Bool) (g : (I → Bool) → ℝ) :
    uniformMean (fun a => g (T a))=
      ∑ ε : I → Bool, g ε * uniformMean (fun a => if T a=ε then 1 else 0) := by
  have he (a : A) : g (T a)=∑ ε : I → Bool, g ε*(if T a=ε then 1 else 0) := by simp
  simp_rw [he]
  rw [uniformMean_sum]
  apply Finset.sum_congr rfl
  intro ε _
  rw [uniformMean_mul]

private instance certificate_instance_0955 : OAI.SidorenkoCounterexample.ProofCertificate_0955 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0955 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6

end Boolean
section Convergence
variable {I Q : Type} [Fintype I] [DecidableEq I] {l : Filter Q}
  {A : Q → Type} [∀ q, Fintype (A q)] [∀ q, Nonempty (A q)]
theorem certificate_proof_0956 (T : (q : Q) → A q → I → Bool)
    (h : ∀ F : Finset I, F.Nonempty → Tendsto
      (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
    (ε : I → Bool) : Tendsto
      (fun q => uniformMean (fun a => if T q a=ε then 1 else 0)) l
        (nhds ((Fintype.card (I → Bool) : ℝ)⁻¹)) := by
  have hm (F : Finset I) : Tendsto
      (fun q => (uniformMean fun a => boolMonomial F (T q a))*boolMonomial F ε) l
        (nhds (if F=∅ then (1:ℝ) else 0)) := by
    by_cases hF : F=∅
    · subst F; simp only [boolMonomial_empty,uniformMean_const,mul_one,↓reduceIte]; exact tendsto_const_nhds
    · simpa only [hF,ite_false,zero_mul] using (h F (Finset.nonempty_iff_ne_empty.mpr hF)).mul_const (boolMonomial F ε)
  have hs := (tendsto_finsetSum Finset.univ (fun F _ => hm F)).const_mul ((2^Fintype.card I : ℝ)⁻¹)
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one] at hs
  simp only [bool_law_expansion,Fintype.card_fun,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]
  exact hs

private instance certificate_instance_0956 : OAI.SidorenkoCounterexample.ProofCertificate_0956 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0956 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0957 (T : (q : Q) → A q → I → Bool)
    (h : ∀ F : Finset I, F.Nonempty → Tendsto
      (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
    (g : (I → Bool) → ℝ) : Tendsto
      (fun q => uniformMean (fun a => g (T q a))) l (nhds (uniformMean g)) := by
  have hm (ε : I → Bool) := (boolean_law_tendsto T h ε).const_mul (g ε)
  have hs := tendsto_finsetSum Finset.univ (fun ε _ => hm ε)
  have he (q : Q) : uniformMean (fun a => g (T q a)) =
      ∑ ε : I → Bool, g ε * uniformMean (fun a => if T q a=ε then 1 else 0) :=
    uniformMean_test_fibers (T q) g
  simp only [he]
  convert hs using 1
  simp only [uniformMean,div_eq_mul_inv,Finset.sum_mul]

private instance certificate_instance_0957 : OAI.SidorenkoCounterexample.ProofCertificate_0957 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0957 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end Convergence
theorem certificate_proof_0958 (D : ℕ) (hD : Even D) (hbig : 12≤D) (g : (Fin 33 → Bool) → ℝ) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      g (pairBool X))) primeInfinity (nhds (uniformMean g)) := by
  have hm (F : Finset (Fin 33)) (hF : F.Nonempty) :
      Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
        boolMonomial F (pairBool X))) primeInfinity (nhds 0) := by
    simpa only [boolMonomial] using pairBool_moment_tendsto D hD hbig F hF
  exact boolean_test_tendsto (I := Fin 33) (Q := OddPrime) (l := primeInfinity)
    (A := fun q : OddPrime => Fin 13 → SymMatrix (ZMod q.val) D)
    (fun (q : OddPrime) (X : Fin 13 → SymMatrix (ZMod q.val) D) => pairBool X) hm g

private instance certificate_instance_0958 : OAI.SidorenkoCounterexample.ProofCertificate_0958 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0958 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Means
variable {K I W : Type} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
include K in
theorem certificate_proof_0959 (v : Fin 3 → I) (hv : Function.Injective v) (f : W → W → ℝ) :
    uniformMean (fun X : I → W => f (X (v 0)-X (v 1)) (X (v 0)-X (v 2)))=
      uniformMean (fun B : W => uniformMean (f B)) := by
  let k : Fin 2 → I := fun j => v j.succ
  have hk : Function.Injective k := hv.comp (Fin.succ_injective 2)
  have hn : ∀ j, k j≠v 0 := fun j => hv.ne (Fin.succ_ne_zero j)
  have he := uniformMean_starDifference (K := K) (W := W) (v 0) k hk hn (fun M => f (M 0) (M 1))
  change uniformMean (fun X : I → W => f (X (v 0)-X (v 1)) (X (v 0)-X (v 2))) =
    uniformMean (fun M : Fin 2 → W => f (M 0) (M 1)) at he
  rw [he,←uniformMean_equiv (finTwoArrowEquiv W).symm,uniformMean_prod]
  rfl

private instance certificate_instance_0959 : OAI.SidorenkoCounterexample.ProofCertificate_0959 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0959 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end Means
section Bounds
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0960 (r : ℕ) (ξ : Fin 3 → ℤ) : 1≤faceBound (K := K) r ξ := by
  have := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 1)
  have := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 2)
  have := pairCoefficient_nonneg (K := K) r (ξ 1) (ξ 2)
  have := tripleCoefficient_nonneg (K := K) r (ξ 0) (ξ 1) (ξ 2)
  unfold faceBound; linarith

private instance certificate_instance_0960 : OAI.SidorenkoCounterexample.ProofCertificate_0960 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0960 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0961 (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : 0≤faceLocal r T ξ X := by
  exact uniformMean_nonneg fun Y => Finset.prod_nonneg fun k _ => rankKernel_nonneg ..

private instance certificate_instance_0961 : OAI.SidorenkoCounterexample.ProofCertificate_0961 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0961 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0962 (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    faceLocal r T ξ X≤faceBound (K := K) r ξ := by
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  have n01 := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 1)
  have n02 := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 2)
  have n12 := pairCoefficient_nonneg (K := K) r (ξ 1) (ξ 2)
  have nt := tripleCoefficient_nonneg (K := K) r (ξ 0) (ξ 1) (ξ 2)
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · subst T; rw [faceLocal_empty]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_pair r ξ X 0 1 (by decide)]
    exact (pairLocal_bound r (ξ 0) (ξ 1) _ hX.1).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_pair r ξ X 0 2 (by decide)]
    exact (pairLocal_bound r (ξ 0) (ξ 2) _ hX.2.1).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_pair r ξ X 1 2 (by decide)]
    exact (pairLocal_bound r (ξ 1) (ξ 2) _ hX.2.2).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_full]
    exact (tripleLocal_bound hK r (hξ 0) (hξ 1) (hξ 2) _ _ hX.1 hX.2.1 (by rw [he]; exact hX.2.2)).trans
      (by unfold faceBound; linarith)

private instance certificate_instance_0962 : OAI.SidorenkoCounterexample.ProofCertificate_0962 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0962 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0963 (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
    (B : SymMatrix K (2*r)) : |pairPolynomial r ξ ζ B|≤2 := by
  by_cases hb : B.val.det=0
  · unfold pairPolynomial; rw [hb]; norm_num
  · rw [pairPolynomial_eq r hξ hζ B hb]; split <;> norm_num

private instance certificate_instance_0963 : OAI.SidorenkoCounterexample.ProofCertificate_0963 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0963 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0964 (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)) :
    |facePolynomial r T ξ X|≤8 := by
  have hpair (k l : Fin 3) : |if k∈T ∧ l∈T then pairPolynomial r (ξ k) (ξ l) (X k-X l) else 1|≤2 := by
    split
    · exact pairPolynomial_abs_le r (hξ k) (hξ l) _
    · norm_num
  unfold facePolynomial
  rw [abs_mul,abs_mul]
  have ha := mul_le_mul (hpair 0 1) (hpair 0 2) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hb := mul_le_mul ha (hpair 1 2) (abs_nonneg _) (by norm_num : (0:ℝ)≤2*2)
  norm_num only at hb
  exact hb

private instance certificate_instance_0964 : OAI.SidorenkoCounterexample.ProofCertificate_0964 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0964 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8

end Bounds
theorem certificate_proof_0965 (r : ℕ) (hr : 0<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) :
    Tendsto (fun q : OddPrime => faceBound (K := ZMod q.val) r ξ) primeInfinity (nhds 29) := by
  have h01 := pairCoefficient_tendsto r hr (hξ 0) (hξ 1)
  have h02 := pairCoefficient_tendsto r hr (hξ 0) (hξ 2)
  have h12 := pairCoefficient_tendsto r hr (hξ 1) (hξ 2)
  have ht := tripleCoefficient_tendsto r hr (hξ 0) (hξ 1) (hξ 2)
  simpa only [faceBound,show (1:ℝ)+4+4+4+16=29 by norm_num] using
    (((h01.const_add 1).add h02).add h12).add ht

private instance certificate_instance_0965 : OAI.SidorenkoCounterexample.ProofCertificate_0965 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0965 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3

theorem certificate_proof_0966 (r : ℕ) (hr : 1<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (v : Fin 3 → Fin 13) (hv : Function.Injective v) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
      faceError r ξ (X ∘ v))) primeInfinity (nhds 0) := by
  have he (q : OddPrime) : uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
      faceError r ξ (X ∘ v)) = uniformMean (pairError (K := ZMod q.val) r (ξ 0) (ξ 1))+
        uniformMean (pairError (K := ZMod q.val) r (ξ 0) (ξ 2))+
        uniformMean (pairError (K := ZMod q.val) r (ξ 1) (ξ 2))+
        uniformMean (fun B => uniformMean (fun C => tripleError (K := ZMod q.val) r (ξ 0) (ξ 1) (ξ 2) B C)) := by
    simp only [faceError,Function.comp_def,uniformMean_add]
    rw [uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 0) (ξ 1)),
      uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 0) (ξ 2)),
      uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 1) (ξ 2)),
      uniformMean_two_differences (K := ZMod q.val) v hv (tripleError r (ξ 0) (ξ 1) (ξ 2))]
  simp only [he]
  have h := (((pairError_tendsto r (by omega) (hξ 0) (hξ 1)).add
    (pairError_tendsto r (by omega) (hξ 0) (hξ 2))).add
    (pairError_tendsto r (by omega) (hξ 1) (hξ 2))).add
    (tripleError_tendsto r hr (hξ 0) (hξ 1) (hξ 2))
  simpa only [add_zero] using h

private instance certificate_instance_0966 : OAI.SidorenkoCounterexample.ProofCertificate_0966 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0966 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section ChartFace
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0967 (D r : ℕ) (A Y : CanonicalLag (K := K) D) :
    0≤canonicalKernel D r A Y := by
  unfold canonicalKernel canonicalStratumMass
  split <;> positivity

private instance certificate_instance_0967 : OAI.SidorenkoCounterexample.ProofCertificate_0967 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0967 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0968 (r : ℕ) (ξ : ℤ) (A Y : SymMatrix K (2*r)) {C : ℝ}
    (hC : 0≤C) (hξ : canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r ξ≤C) :
    rankKernel K (2*r) r ξ (A-Y) ≤ C*canonicalKernel (2*r) r (matrixLagrangian A) (matrixLagrangian Y) := by
  have hm := canonicalStratumMass_pos (K := K) (2*r) r (by omega)
  unfold rankKernel
  split_ifs with hAY
  · have hrank : (A-Y).val.rank=r := (Finset.mem_filter.mp hAY).2.1
    have hdim := matrixLagrangian_pair_rank (2*r) A Y
    have hi : finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian Y).val)=r := by omega
    rw [canonicalKernel,if_pos hi]
    have he : (layerMass K (2*r) r ξ)⁻¹ =
        (canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r ξ) *
          (canonicalStratumMass (K := K) (2*r) r)⁻¹ := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right hξ (inv_nonneg.mpr hm.le)
  · exact mul_nonneg hC (canonicalKernel_nonneg ..)

private instance certificate_instance_0968 : OAI.SidorenkoCounterexample.ProofCertificate_0968 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0968 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0969 (D r : ℕ) (L : Fin 3 → CanonicalLag (K := K) D)
    (T : Finset (Fin 3)) (Y : CanonicalLag (K := K) D) :
    (∏ i∈T, canonicalKernel D r (L i) Y)=
      (if ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r then 1 else 0)*
        ((canonicalStratumMass (K := K) D r)⁻¹)^T.card := by
  by_cases h : ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r
  · rw [if_pos h,one_mul]
    calc
      _ = ∏ _i∈T, (canonicalStratumMass (K := K) D r)⁻¹ :=
        Finset.prod_congr rfl (fun i hi => by rw [canonicalKernel,if_pos (h i hi)])
      _ = _ := by rw [Finset.prod_const]
  · rw [if_neg h,zero_mul]
    push Not at h
    obtain ⟨i,hi,hh⟩ := h
    exact Finset.prod_eq_zero hi (by rw [canonicalKernel,if_neg hh])

private instance certificate_instance_0969 : OAI.SidorenkoCounterexample.ProofCertificate_0969 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0969 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0970 (D r : ℕ) [Fintype (CanonicalLag (K := K) D)]
    (L : Fin 3 → CanonicalLag (K := K) D) (T : Finset (Fin 3)) :
    uniformMean (fun Y => ∏ i∈T, canonicalKernel D r (L i) Y)=
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin D → K)) r
        (verticalLagrangian (K := K) (V := Fin D → K)) L T := by
  simp_rw [canonicalKernel_prod]
  rw [uniformMean_mul_right,uniformMean_indicator]
  unfold activeFaceDensity canonicalStratumMass
  simp only [inv_div,Nat.card_eq_fintype_card]
  rfl

private instance certificate_instance_0970 : OAI.SidorenkoCounterexample.ProofCertificate_0970 := by
  constructor
  intro c0 c1 c2 c3 q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0970 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0971 (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
    (hξ : ∀ i∈T, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ i)≤C) :
    faceLocal r T ξ X ≤ C^3 * lagrangianConstant (2*r) *
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (matrixLagrangian ∘ X) T := by
  let :=  Fintype.ofFinite (CanonicalLag (K := K) (2*r))
  let : Nonempty (CanonicalLag (K := K) (2*r)) := ⟨verticalLagrangian⟩
  let f (Y : CanonicalLag (K := K) (2*r)) := ∏ i∈T, canonicalKernel (2*r) r (matrixLagrangian (X i)) Y
  have hf (Y) : 0≤f Y := Finset.prod_nonneg (fun i _ => canonicalKernel_nonneg ..)
  have hp (Y : SymMatrix K (2*r)) : (∏ i∈T,rankKernel K (2*r) r (ξ i) (X i-Y))≤C^3*f (matrixLagrangian Y) := by
    calc
      _ ≤ ∏ i∈T,C*canonicalKernel (2*r) r (matrixLagrangian (X i)) (matrixLagrangian Y) :=
        Finset.prod_le_prod (fun _ _ => rankKernel_nonneg ..)
          (fun i hi => rankKernel_chart_bound r (ξ i) (X i) Y (by linarith) (hξ i hi))
      _ = C^T.card*f (matrixLagrangian Y) := by rw [Finset.prod_mul_distrib,Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by have := Finset.card_le_univ T; simpa using this)) (hf _)
  have hi := uniformMean_injection (matrixLagrangian (K := K) (D := 2*r))
    (matrixLagrangian_injective (2*r)) f hf
  have he : ((Fintype.card (CanonicalLag (K := K) (2*r)) : ℝ)/Fintype.card (SymMatrix K (2*r)))=
      chartRatio (K := K) (2*r) := by rw [chartRatio,Nat.card_eq_fintype_card]
  rw [he] at hi
  change faceLocal r T ξ X ≤ _
  calc
    _ ≤ C^3*uniformMean (f ∘ matrixLagrangian) := by
      rw [←uniformMean_mul]; exact uniformMean_mono hp
    _ ≤ C^3*(chartRatio (K := K) (2*r)*uniformMean f) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ C^3*(lagrangianConstant (2*r)*uniformMean f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (chartRatio_bound (2*r)) (uniformMean_nonneg hf)) (by positivity)
    _ = _ := by rw [show uniformMean f=activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (matrixLagrangian ∘ X) T from canonicalKernel_mean (2*r) r _ T]; ring

private instance certificate_instance_0971 : OAI.SidorenkoCounterexample.ProofCertificate_0971 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0971 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end ChartFace
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
theorem certificate_proof_0972 : ∀ j k,
    pairLeft (facePair j k)=faceVertex j (slotLeft k) ∧
    pairRight (facePair j k)=faceVertex j (slotRight k) := by decide

private instance certificate_instance_0972 : OAI.SidorenkoCounterexample.ProofCertificate_0972 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0972 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1

theorem certificate_proof_0973 (e : Fin 33) : pairVertices e∈modelPointPairs := by
  have h : ∀ e,∃ j,pairVertices e⊆faces j := by decide
  obtain ⟨j,hj⟩ := h e
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_powersetCard.mpr ⟨hj,pairVertices_card e⟩⟩

private instance certificate_instance_0973 : OAI.SidorenkoCounterexample.ProofCertificate_0973 := by
  constructor
  intro q0
  exact @certificate_proof_0973 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0

theorem certificate_proof_0974 : ∀ j, (faces j).powersetCard 2 =
    Finset.univ.image (fun k => pairVertices (facePair j k)) := by decide

private instance certificate_instance_0974 : OAI.SidorenkoCounterexample.ProofCertificate_0974 := by
  constructor
  intro q0
  exact @certificate_proof_0974 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0

theorem certificate_proof_0975 (e : Finset (Fin 13)) (he : e∈modelPointPairs) : ∃ k,pairVertices k=e := by
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp he
  rw [face_pairs_image] at hj
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hj
  exact ⟨facePair j k,hk⟩

private instance certificate_instance_0975 : OAI.SidorenkoCounterexample.ProofCertificate_0975 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0975 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1

theorem certificate_proof_0976 {K : Type} [Field K] {r : ℕ} (X : Fin 13 → SymMatrix K (2*r))
    (hX : fullTransverse X) (j : Fin 22) : faceTransverse r (X ∘ faceVertex j) := by
  have h (k : Fin 3) := hX (facePair j k)
  simp only [(facePair_endpoints j _).1,(facePair_endpoints j _).2] at h
  exact ⟨h 0,h 1,h 2⟩

private instance certificate_instance_0976 : OAI.SidorenkoCounterexample.ProofCertificate_0976 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0976 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5

section FaceGraph
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0977 {D : ℕ} (X : Fin 13 → SymMatrix K D) (hX : fullTransverse X) (e : Fin 33) :
    boolSign (pairBool X e)=pairSign X e := by
  have h := pairBool_error X e
  rw [pairSingular,if_neg (hX e)] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

private instance certificate_instance_0977 : OAI.SidorenkoCounterexample.ProofCertificate_0977 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0977 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0978 (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) (j : Fin 22) :
    facePolynomial r T ξ (X ∘ faceVertex j)=
      boolFacePolynomial (quadraticChar K ((-1 : K)^r)) T ξ j (pairBool X) := by
  unfold boolFacePolynomial
  simp_rw [pairBool_eq_sign X hX,pairSign,(facePair_endpoints j _).1,(facePair_endpoints j _).2]
  simp only [Fin.prod_univ_three,slotLeft,slotRight,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,facePolynomial,pairPolynomial,Function.comp_def]
  rfl

private instance certificate_instance_0978 : OAI.SidorenkoCounterexample.ProofCertificate_0978 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0978 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end FaceGraph
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Global
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0979 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) :
    0≤configurationProduct r T ξ X := Finset.prod_nonneg (fun _ _ => faceLocal_nonneg ..)

private instance certificate_instance_0979 : OAI.SidorenkoCounterexample.ProofCertificate_0979 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0979 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0980 (r : ℕ) (X : Fin 13 → SymMatrix K (2*r)) :
    canonicalSingular (2*r) (matrixLagrangian ∘ X) ↔ ¬fullTransverse X := by
  unfold canonicalSingular fullTransverse
  rw [not_forall]
  apply exists_congr
  intro e
  rw [pair_endpoints,Finset.inf_insert,Finset.inf_singleton]
  exact not_congr (matrixLagrangian_pair_zero (2*r) (X (pairLeft e)) (X (pairRight e)))

private instance certificate_instance_0980 : OAI.SidorenkoCounterexample.ProofCertificate_0980 := by
  constructor
  intro c0 q0 q1 q2 q3
  exact @certificate_proof_0980 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0981 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (L : Fin 13 → CanonicalLag (K := K) (2*r)) : 0≤canonicalConfiguration r T L :=
  Finset.prod_nonneg (fun _ _ => activeFaceDensity_nonneg ..)

private instance certificate_instance_0981 : OAI.SidorenkoCounterexample.ProofCertificate_0981 := by
  constructor
  intro c0 c1 c2 c3 q0 q1 q2 q3 q4
  exact @certificate_proof_0981 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4

theorem certificate_proof_0982 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
    (hξ : ∀ j i, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ j i)≤C) :
    configurationProduct r T ξ X ≤ (C^3*lagrangianConstant (2*r))^22 *
      canonicalConfiguration r T (matrixLagrangian ∘ X) := by
  calc
    _ ≤ ∏ j : Fin 22, (C^3*lagrangianConstant (2*r))*
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K))
          (matrixLagrangian ∘ (X ∘ faceVertex j)) (T j) :=
      Finset.prod_le_prod (fun _ _ => faceLocal_nonneg ..)
        (fun j _ => faceLocal_chart_bound r (T j) (ξ j) _ hC (fun i _ => hξ j i))
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rfl

private instance certificate_instance_0982 : OAI.SidorenkoCounterexample.ProofCertificate_0982 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0982 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

omit [DecidableEq K] in
theorem certificate_proof_0983 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    [Fintype (CanonicalLag (K := K) (2*r))] :
    actualSingularTail (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
      (verticalLagrangian (K := K) (V := Fin (2*r) → K)) T =
      uniformMean (fun L : Fin 13 → CanonicalLag (K := K) (2*r) =>
        if canonicalSingular (2*r) L then canonicalConfiguration r T L else 0) := by
  have hi : Fintype.ofFinite (Fin 13 → CanonicalLag (K := K) (2*r)) =
      (inferInstance : Fintype (Fin 13 → CanonicalLag (K := K) (2*r))) := Subsingleton.elim _ _
  unfold actualSingularTail uniformMean
  rw [hi]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.card_eq_fintype_card]
  congr 1
  apply Finset.sum_congr rfl
  intro L _
  unfold canonicalSingular canonicalConfiguration
  split_ifs <;> rfl

private instance certificate_instance_0983 : OAI.SidorenkoCounterexample.ProofCertificate_0983 := by
  constructor
  intro c0 c1 c2 c3 q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0983 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0984 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) {C : ℝ} (hC : 1≤C)
    (hξ : ∀ j i, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ j i)≤C) :
    matrixSingularTail (K := K) r T ξ ≤
      ((C^3*lagrangianConstant (2*r))^22*lagrangianConstant (2*r)^13)*
        actualSingularTail (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
          (verticalLagrangian (K := K) (V := Fin (2*r) → K)) T := by
  let := Fintype.ofFinite (CanonicalLag (K := K) (2*r))
  let : Nonempty (CanonicalLag (K := K) (2*r)) := ⟨verticalLagrangian⟩
  let f (L : Fin 13 → CanonicalLag (K := K) (2*r)) :=
    if canonicalSingular (2*r) L then canonicalConfiguration r T L else 0
  have hf (L) : 0≤f L := by dsimp only [f]; split <;> simp only [canonicalConfiguration_nonneg,le_refl]
  have hj : Function.Injective (fun X : Fin 13 → SymMatrix K (2*r) => matrixLagrangian ∘ X) := by
    intro X Y h; funext i; exact matrixLagrangian_injective (2*r) (congrFun h i)
  have hi := uniformMean_injection (fun X : Fin 13 → SymMatrix K (2*r) => matrixLagrangian ∘ X) hj f hf
  have he : ((Fintype.card (Fin 13 → CanonicalLag (K := K) (2*r)) : ℝ)/
      Fintype.card (Fin 13 → SymMatrix K (2*r)))=(chartRatio (K := K) (2*r))^13 := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,chartRatio,Nat.card_eq_fintype_card,div_pow]
  rw [he] at hi
  have hp (X : Fin 13 → SymMatrix K (2*r)) :
      (if fullTransverse X then 0 else configurationProduct r T ξ X)≤
        (C^3*lagrangianConstant (2*r))^22*f (matrixLagrangian ∘ X) := by
    dsimp only [f]
    rw [canonicalSingular_chart]
    by_cases hx : fullTransverse X
    · simp only [hx,ite_true,not_true_eq_false,ite_false,mul_zero,le_refl]
    · simp only [hx,ite_false,not_false_eq_true,ite_true]
      exact configuration_chart_bound r T ξ X hC hξ
  have hC0 : 0≤(C^3*lagrangianConstant (2*r))^22 := by positivity
  calc
    _ ≤ (C^3*lagrangianConstant (2*r))^22*uniformMean (fun X => f (matrixLagrangian ∘ X)) := by
      rw [←uniformMean_mul]; exact uniformMean_mono hp
    _ ≤ (C^3*lagrangianConstant (2*r))^22*(chartRatio (K := K) (2*r)^13*uniformMean f) :=
      mul_le_mul_of_nonneg_left hi hC0
    _ ≤ (C^3*lagrangianConstant (2*r))^22*(lagrangianConstant (2*r)^13*uniformMean f) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (chartRatio_nonneg (2*r)) (chartRatio_bound (2*r)) _) (uniformMean_nonneg hf)) hC0
    _ = _ := by rw [actualSingularTail_uniform,mul_assoc]

private instance certificate_instance_0984 : OAI.SidorenkoCounterexample.ProofCertificate_0984 := by
  constructor
  intro c0 c1 c2 c3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0984 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end Global
theorem certificate_proof_0985 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (hlarge : singularTailThreshold≤2*r) : Tendsto
      (fun q : OddPrime => actualSingularTail (canonicalSymplectic (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)) r
        (verticalLagrangian (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)) T)
      primeInfinity (nhds 0) := by
  have ht := (integratedTailMajorant_tendsto_zero (2*r) r (fun j => decide (T j=Finset.univ))
    (singularTailThreshold_large.trans hlarge)).comp primeInfinity_real_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun q => actualSingularTail_nonneg _ r _ T)) _ ht
  filter_upwards [primeInfinity_real_tendsto.eventually (eventually_ge_atTop (4*lagrangianConstant (2*r)))] with q hq
  have h2 : (2 : ZMod q.val)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using q.property.2)
  let : Invertible (2 : ZMod q.val) := invertibleOfNonzero h2
  have hD : 2*(2*r)=finrank (ZMod q.val)
      ((Fin (2*r) → ZMod q.val) × Module.Dual (ZMod q.val) (Fin (2*r) → ZMod q.val)) := by
    rw [Module.finrank_prod,Subspace.dual_finrank_eq,Module.finrank_pi,Fintype.card_fin]; omega
  have h := actualSingularTail_bound
    (canonicalSymplectic (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val))
    canonicalSymplectic_nondegenerate (2*r) hD h2 canonicalSymplectic_alt r rfl hlarge
    (by simpa only [ZMod.card] using hq) verticalLagrangian T
  simpa only [Function.comp_def,ZMod.card] using h

private instance certificate_instance_0985 : OAI.SidorenkoCounterexample.ProofCertificate_0985 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2
  exact @certificate_proof_0985 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2

theorem certificate_proof_0986 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i, ξ j i=1 ∨ ξ j i= -1)
    (hlarge : singularTailThreshold≤2*r) : Tendsto
      (fun q : OddPrime => matrixSingularTail (K := ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  have hr : 0<r := by have := singularTailThreshold_large; omega
  let C : ℝ := 4*2^r
  have hC : 1≤C := by dsimp [C]; have : 1≤(2:ℝ)^r := one_le_pow₀ (by norm_num); linarith
  have he : ∀ᶠ q : OddPrime in primeInfinity, ∀ j i,
      canonicalStratumMass (K := ZMod q.val) (2*r) r / layerMass (ZMod q.val) (2*r) r (ξ j i)≤C := by
    rw [eventually_all]; intro j; rw [eventually_all]; intro i
    exact signed_normalization_eventually r hr (hξ j i)
  have ht := (canonicalTail_tendsto r T hlarge).const_mul
    ((C^3*lagrangianConstant (2*r))^22*lagrangianConstant (2*r)^13)
  simp only [mul_zero] at ht
  have hn (q : OddPrime) : 0 ≤ matrixSingularTail (K := ZMod q.val) r T ξ := by
    unfold matrixSingularTail
    apply uniformMean_nonneg
    intro X
    split
    · rfl
    · exact configurationProduct_nonneg ..
  apply squeeze_zero' (Eventually.of_forall hn) _ ht
  filter_upwards [he] with q hq
  exact matrixSingularTail_bound r T ξ hC hq

private instance certificate_instance_0986 : OAI.SidorenkoCounterexample.ProofCertificate_0986 := by
  constructor
  intro c0 q0 q1 q2 q3 q4
  exact @certificate_proof_0986 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section GlobalProduct
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0987 (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) : 8≤globalBound (K := K) r ξ := by
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 22)))
    (fun j _ => le_trans (by norm_num : (0:ℝ)≤1) (faceBound_one (K := K) r (ξ j)))
  unfold globalBound; linarith

private instance certificate_instance_0987 : OAI.SidorenkoCounterexample.ProofCertificate_0987 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0987 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 q0 q1 q2 q3 q4 q5

end GlobalProduct
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section GlobalBool
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end GlobalBool
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
variable {A B C I : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section BooleanMoments
variable {K : Type} [Fintype K] [DecidableEq K]
end BooleanMoments
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0953 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0954 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0955 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0956 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0957 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0958 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0959 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0960 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0961 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0962 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0963 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0964 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0965 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0966 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0967 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0968 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0969 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0970 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0971 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0972 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0973 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0974 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0975 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0976 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0977 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0978 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0979 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0980 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0981 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0982 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0983 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0984 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0985 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0986 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0987 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

