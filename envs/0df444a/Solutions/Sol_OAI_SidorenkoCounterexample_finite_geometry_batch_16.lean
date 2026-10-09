-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_16
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:23:54.543032+00:00
-- url     : https://prove2.me/submissions/5921c336-bbac-4b65-bab2-06b2abe5e6a7

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0011]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0042]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0045]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0059]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0071]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0219]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0345]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0346]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0347]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0348]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0352]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0355]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0356]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0357]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0358]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0359]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0360]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0363]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0368]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0369]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0375]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0378]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0379]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0380]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0386]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0387]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0388]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0389]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0390]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33

namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0391 (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0) :
    ∀ e, h e ≤ tailPairBound := by
  let M : ℝ := (Finset.univ.sup h:ℕ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hb := global_tail_budget D full a h ha htotal
  change (∑ j, tailEnergy D (full j) (a j))+separationExcess h ≤ 33*M at hb
  have he0 : 0 ≤ separationExcess h := separationExcess_nonneg h
  have hen (j : Fin 22) : 0 ≤ tailEnergy D (full j) (a j) := tailEnergy_nonneg (ha.1 j)
  have hes : 0 ≤ ∑ j, tailEnergy D (full j) (a j) := Finset.sum_nonneg (fun j _ => hen j)
  have he (j : Fin 22) : tailEnergy D (full j) (a j) ≤ 33*M := by
    have hh := Finset.single_le_sum (fun j _ => hen j) (Finset.mem_univ j)
    linarith
  have hroot : (h 0:ℝ)^2 ≤ 198*M := by linarith [separationExcess_root h]
  have hstep (e : Fin 33) : ((h e:ℝ)-h (pairParent e))^2 ≤ 22572*M := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    have hh := tail_pair_energy (ha.1 (pairBridge e)) i k
    rw [ha.2,ha.2,hi,hk] at hh
    linarith [he (pairBridge e)]
  obtain ⟨em,_,hem⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty h
  have hem' : (h em:ℝ)=M := by
    dsimp [M]; exact_mod_cast hem.symm
  have hg := parent_energy_bound pairParent pairParent_lt (fun e => (h e:ℝ)) (22572*M) (by positivity) hstep em
  have hp : (4:ℝ)^em.val ≤ (4:ℝ)^32 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hgp := mul_le_mul_of_nonneg_right hp (show 0 ≤ 22572*M by positivity)
  have htotalM : M^2 ≤ (tailPairBound:ℝ)*M := by
    rw [hem'] at hg
    simp only [tailPairBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [hg,hgp,hroot,sq_nonneg (M-2*(h 0:ℝ))]
  have hMB : M ≤ (tailPairBound:ℝ) := by
    by_contra hnot
    have hdiff : 0 < M-(tailPairBound:ℝ) := by linarith
    have hMp : 0 < M := lt_of_le_of_lt (Nat.cast_nonneg _) (lt_of_not_ge hnot)
    have hp := mul_pos hMp hdiff
    nlinarith only [hp,htotalM]
  intro e
  have heM : (h e:ℝ) ≤ M := by
    dsimp [M]; exact_mod_cast (Finset.le_sup (f := h) (Finset.mem_univ e))
  exact_mod_cast heM.trans hMB

private instance certificate_instance_0391 : OAI.SidorenkoCounterexample.ProofCertificate_0391 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0391 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0392 (B : ℕ) : 0 ≤ tailRemainderBound B :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private instance certificate_instance_0392 : OAI.SidorenkoCounterexample.ProofCertificate_0392 := by
  constructor
  intro q0
  exact @certificate_proof_0392 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0

theorem certificate_proof_0393 (D : ℕ) (a : TailTuple) :
    tailSlack D true a=tailLinear a*((D:ℝ)-a.c)+tailRemainder a := by
  simp only [tailSlack,tailGain,ite_true,a.baseline D]
  rw [slack_leading_coefficient]
  dsimp [tailLinear,tailRemainder,TailTuple.delta]
  ring

private instance certificate_instance_0393 : OAI.SidorenkoCounterexample.ProofCertificate_0393 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0393 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1

theorem certificate_proof_0394 {a : TailTuple} (hu : a.u ≤ a.c) : 0 ≤ tailLinear a := by
  have hu' : (a.u:ℝ) ≤ a.c := by exact_mod_cast hu
  dsimp [tailLinear]
  linarith [show (0:ℝ) ≤ a.v by positivity]

private instance certificate_instance_0394 : OAI.SidorenkoCounterexample.ProofCertificate_0394 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0394 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1

theorem certificate_proof_0395 {a : TailTuple} (hu : a.u ≤ a.c)
    (hbad : ¬(a.u=a.c ∧ a.v=0)) : 1/2 ≤ tailLinear a := by
  have hh : a.u+1 ≤ a.c+a.v := by omega
  have hh' : (a.u:ℝ)+1 ≤ a.c+a.v := by exact_mod_cast hh
  dsimp [tailLinear]; linarith

private instance certificate_instance_0395 : OAI.SidorenkoCounterexample.ProofCertificate_0395 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0395 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2

theorem certificate_proof_0396 {D B : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) (hB : a.maxH ≤ B) :
    |tailRemainder a| ≤ tailRemainderBound B := by
  have hc : a.c ≤ B := a.c_le_max.trans hB
  have hu : a.u ≤ B := (ha.2.2 rfl).1.trans hc
  have hv : a.v ≤ B := ha.v_le_max.trans hB
  have hp (i : Fin 3) : a.p i ≤ B := (a.p_le_h i).trans ((a.h_le_max i).trans hB)
  have ht (i : Fin 3) : a.t i ≤ B := (a.t_le_h i).trans ((a.h_le_max i).trans hB)
  let b : TailBox B := ⟨⟨a.c,by omega⟩,⟨a.u,by omega⟩,⟨a.v,by omega⟩,
    fun i => ⟨a.p i,by have := hp i; omega⟩,fun i => ⟨a.t i,by have := ht i; omega⟩⟩
  have hb : b.tuple=a := by cases a; rfl
  rw [←hb]
  exact Finset.single_le_sum (f := fun x : TailBox B => |tailRemainder x.tuple|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ b)

private instance certificate_instance_0396 : OAI.SidorenkoCounterexample.ProofCertificate_0396 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0396 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4

theorem certificate_proof_0397 {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D false a) : 0 ≤ tailSlack D false a := by
  obtain ⟨k,hk⟩ := a.exists_max
  have hsk (i : Fin 3) : a.s i ≤ a.s k := by
    have hh := a.h_le_max i
    rw [hk] at hh
    exact Nat.le_of_add_le_add_left hh
  exact (lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
    (by rw [hk]; rfl)).1

private instance certificate_instance_0397 : OAI.SidorenkoCounterexample.ProofCertificate_0397 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0397 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2

theorem certificate_proof_0398 {D : ℕ} {full : Fin 22 → Bool} {a : Fin 22 → TailTuple}
    {h : Fin 33 → ℕ} (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0) (j : Fin 22) :
    (a j).maxH ≤ tailPairBound := by
  have hb := global_tail_pair_bound D full a h ha htotal
  apply Finset.sup_le
  intro k _
  rw [ha.2]
  exact hb _

private instance certificate_instance_0398 : OAI.SidorenkoCounterexample.ProofCertificate_0398 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0398 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0399 : ∃ D₀ : ℕ, ∀ D ≥ D₀,
    ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
    GlobalTailFeasible D full a h →
    (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0 →
    ∀ j, full j=true → (a j).u=(a j).c ∧ (a j).v=0 := by
  let B := tailPairBound
  let R := tailRemainderBound B
  have hR : 0 ≤ R := tailRemainderBound_nonneg B
  obtain ⟨D₀,hD₀⟩ := exists_nat_gt ((B:ℝ)+44*R)
  refine ⟨D₀,?_⟩
  intro D hD full a h ha htotal
  have hD' : (B:ℝ)+44*R < D := lt_of_lt_of_le hD₀ (by exact_mod_cast hD)
  have hB (j : Fin 22) : (a j).maxH ≤ B := global_maxH_bound ha htotal j
  have hc (j : Fin 22) : ((a j).c:ℝ) ≤ B := by
    exact_mod_cast (a j).c_le_max.trans (hB j)
  have hrem (j : Fin 22) (hj : full j=true) : -R ≤ tailRemainder (a j) := by
    have hh := tailRemainder_bounded (D := D) (by simpa only [hj] using ha.1 j) (hB j)
    exact (abs_le.mp hh).1
  have hs (j : Fin 22) : -R ≤ tailSlack D (full j) (a j) := by
    cases hj : full j with
    | false =>
      have hh := tailSlack_lower_nonneg (by simpa only [hj] using ha.1 j)
      linarith only [hR,hh]
    | true =>
      have haj : TailFeasible D true (a j) := by simpa only [hj] using ha.1 j
      rw [tailSlack_linear]
      have hdn : 0 ≤ (D:ℝ)-(a j).c := sub_nonneg.mpr (by exact_mod_cast haj.1)
      have hh := mul_nonneg (tailLinear_nonneg (haj.2.2 rfl).1) hdn
      linarith only [hh,hrem j hj]
  intro j hj
  by_contra hbad
  have haj : TailFeasible D true (a j) := by simpa only [hj] using ha.1 j
  have hA := tailLinear_half (haj.2.2 rfl).1 hbad
  have hdn : 0 ≤ (D:ℝ)-(a j).c := by
    have hcD : ((a j).c:ℝ) ≤ D := by exact_mod_cast haj.1
    linarith
  have hmul := mul_le_mul_of_nonneg_right hA hdn
  have hsl : (D:ℝ)/2-(B:ℝ)/2-R ≤ tailSlack D (full j) (a j) := by
    rw [hj,tailSlack_linear]
    linarith only [hmul,hrem j hj,hc j]
  have hsum : tailSlack D (full j) (a j)+R ≤ ∑ k, (tailSlack D (full k) (a k)+R) :=
    Finset.single_le_sum (f := fun k : Fin 22 => tailSlack D (full k) (a k)+R)
      (fun k _ => by linarith only [hs k]) (Finset.mem_univ j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsum
  linarith only [hsum,hsl,htotal,separationExcess_nonneg h,hD']

private instance certificate_instance_0399 : OAI.SidorenkoCounterexample.ProofCertificate_0399 := by
  constructor
  exact @certificate_proof_0399 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0400 (a : TailTuple) (hu : a.u=a.c) : a.delta=(a.c:ℝ) := by
  dsimp [TailTuple.delta]; rw [hu]; ring

private instance certificate_instance_0400 : OAI.SidorenkoCounterexample.ProofCertificate_0400 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0400 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1

theorem certificate_proof_0401 (D : ℕ) (a : TailTuple) (hu : a.u=a.c) (hv : a.v=0) :
    tailSlack D true a = baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
      plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) := by
  simp only [tailSlack,tailGain,ite_true,a.baseline D,delta_integer_regime a hu,hv,Nat.cast_zero]

private instance certificate_instance_0401 : OAI.SidorenkoCounterexample.ProofCertificate_0401 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0401 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3

theorem certificate_proof_0402 {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) (hu : a.u=a.c) (hv : a.v=0) :
    0 ≤ tailSlack D true a ∧ (tailSlack D true a=0 →
      (a.c=0 ∧ ∀ i, (a.p i=0 ∧ a.t i=0) ∨ (a.p i=1 ∧ a.t i=1)) ∨
      (a.c=1 ∧ ∀ i, a.p i=0 ∧ a.t i=0)) := by
  rw [tailSlack_integer D a hu hv]
  by_cases hc0 : a.c=0
  · have he : baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
        plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) =
        (∑ i : Fin 3, (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1))/6 := by
      rw [slack_integer_regime,hc0]
      simp only [Nat.cast_zero,Fin.sum_univ_three]; ring
    rw [he]
    have hi (i : Fin 3) : 0 ≤ (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1) ∧
        ((2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1)=0 →
          (a.p i=0 ∧ a.t i=0) ∨ (a.p i=1 ∧ a.t i=1)) := by
      have ht := (ha.2.2 rfl).2.1 i
      rw [delta_integer_regime a hu,hc0,Nat.cast_zero,add_zero] at ht
      have ht' : (a.t i:ℤ) ≤ a.p i := by exact_mod_cast ht
      have hh := integer_pair_slack (a.p i) (a.t i) (by positivity) (by positivity) ht'
      refine ⟨by exact_mod_cast hh.1,?_⟩
      intro hz
      have hz' : (2*(a.p i:ℤ)-a.t i)*(2*(a.p i:ℤ)-a.t i-1)=0 := by exact_mod_cast hz
      have hh' := hh.2.mp hz'
      exact_mod_cast hh'
    have hsum : 0 ≤ ∑ i : Fin 3, (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1) :=
      Finset.sum_nonneg (fun i _ => (hi i).1)
    refine ⟨by positivity,fun hz => Or.inl ⟨hc0,?_⟩⟩
    intro i
    apply (hi i).2
    have hh := Finset.single_le_sum (f := fun k : Fin 3 =>
      (2*(a.p k:ℝ)-a.t k)*(2*(a.p k:ℝ)-a.t k-1))
      (fun k _ => (hi k).1) (Finset.mem_univ i)
    linarith only [hh,hz,(hi i).1]
  · by_cases hc1 : a.c=1
    · have he : baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
          plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) =
          (∑ i : Fin 3, ((2*(a.p i:ℝ)-a.t i)^2+3*a.p i))/6 := by
        rw [slack_integer_regime,hc1]
        simp only [Nat.cast_one,Fin.sum_univ_three]; ring
      rw [he]
      have hi (i : Fin 3) : 0 ≤ (2*(a.p i:ℝ)-a.t i)^2+3*a.p i := by positivity
      have hsum : 0 ≤ ∑ i : Fin 3, ((2*(a.p i:ℝ)-a.t i)^2+3*a.p i) :=
        Finset.sum_nonneg (fun i _ => hi i)
      refine ⟨by positivity,fun hz => Or.inr ⟨hc1,?_⟩⟩
      intro i
      have hh := Finset.single_le_sum (f := fun k : Fin 3 =>
        (2*(a.p k:ℝ)-a.t k)^2+3*a.p k) (fun k _ => hi k) (Finset.mem_univ i)
      have hp : a.p i=0 := by
        have hn : (0:ℝ) ≤ a.p i := Nat.cast_nonneg _
        have hz' : (a.p i:ℝ)=0 := by nlinarith only [hh,hz,hn,sq_nonneg (2*(a.p i:ℝ)-a.t i)]
        exact_mod_cast hz'
      refine ⟨hp,?_⟩
      simp only [hp,Nat.cast_zero,mul_zero,add_zero,zero_sub,neg_sq] at hh
      have ht' : (a.t i:ℝ)=0 := by nlinarith only [hh,hz,sq_nonneg (a.t i:ℝ)]
      exact_mod_cast ht'
    · have hc : (2:ℝ) ≤ a.c := by
        have hh : 2 ≤ a.c := by omega
        exact_mod_cast hh
      have hh := slack_pos_of_two_le a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)
        hc (fun i => by positivity)
      exact ⟨hh.le,fun hz => (ne_of_gt hh hz).elim⟩

private instance certificate_instance_0402 : OAI.SidorenkoCounterexample.ProofCertificate_0402 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0402 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4

theorem certificate_proof_0403 {D : ℕ} {a : TailTuple} (ha : TailFeasible D true a)
    (hu : a.u=a.c) (hv : a.v=0) (hz : tailSlack D true a=0) : FaceResidue a := by
  rcases (integer_slack_classification ha hu hv).2 hz with ⟨hc,hh⟩ | ⟨hc,hh⟩
  · left; refine ⟨hc,fun i => ?_⟩
    rcases hh i with ⟨hp,ht⟩ | ⟨hp,ht⟩
    · left; simp only [TailTuple.h,TailTuple.s,hc,hp,ht]
    · right; simp only [TailTuple.h,TailTuple.s,hc,hp,ht]
  · right; refine ⟨hc,fun i => ?_⟩
    simp only [TailTuple.h,TailTuple.s,hc,(hh i).1,(hh i).2]

private instance certificate_instance_0403 : OAI.SidorenkoCounterexample.ProofCertificate_0403 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0403 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0404 {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D false a) (hz : tailSlack D false a=0) : FaceResidue a := by
  obtain ⟨k,hk⟩ := a.exists_max
  have hsk (i : Fin 3) : a.s i ≤ a.s k := by
    have hh := a.h_le_max i
    rw [hk] at hh
    exact Nat.le_of_add_le_add_left hh
  have hh := (lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
    (by rw [hk]; rfl)).2.2 hz
  left; refine ⟨hh.1,fun i => ?_⟩
  by_cases hik : i=k
  · subst i; simpa only [TailTuple.h,hh.1,zero_add] using hh.2.2
  · left; simp only [TailTuple.h,hh.1,hh.2.1 i hik,add_zero]

private instance certificate_instance_0404 : OAI.SidorenkoCounterexample.ProofCertificate_0404 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0404 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3

theorem certificate_proof_0405 {a : TailTuple} (ha : FaceResidue a) (i k : Fin 3) :
    a.h i=1 ↔ a.h k=1 := by
  rcases ha with ⟨_,hh⟩ | ⟨_,hh⟩
  · have hi := hh i; have hk := hh k
    constructor <;> intro h <;> omega
  · rw [hh i,hh k]

private instance certificate_instance_0405 : OAI.SidorenkoCounterexample.ProofCertificate_0405 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0405 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0406 : ∀ e : Fin 33,
    (Finset.univ.filter fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e).card=2 := by decide

private instance certificate_instance_0406 : OAI.SidorenkoCounterexample.ProofCertificate_0406 := by
  constructor
  intro q0
  exact @certificate_proof_0406 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0

theorem certificate_proof_0407 (f : Fin 33 → ℝ) :
    (∑ j : Fin 22, ∑ k : Fin 3, f (facePair j k))=2*∑ e, f e := by
  rw [←Fintype.sum_prod_type (fun p : Fin 22 × Fin 3 => f (facePair p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 22 × Fin 3 => facePair p.1 p.2)]
  have he (e : Fin 33) : (∑ p ∈ Finset.univ.filter (fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e),
      f (facePair p.1 p.2))=2*f e := by
    calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e), f e := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2]
         _ = _ := by rw [Finset.sum_const,pair_incidence_card]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [he]
  rw [Finset.mul_sum]

private instance certificate_instance_0407 : OAI.SidorenkoCounterexample.ProofCertificate_0407 := by
  constructor
  intro q0
  exact @certificate_proof_0407 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0

theorem certificate_proof_0408 (h : Fin 33 → ℕ) (he : separationExcess h=0) : h 0=0 := by
  have hh := separationExcess_root h
  rw [he] at hh
  have h0 : (h 0:ℝ)=0 := by nlinarith [sq_nonneg (h 0:ℝ)]
  exact_mod_cast h0

private instance certificate_instance_0408 : OAI.SidorenkoCounterexample.ProofCertificate_0408 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0408 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1

theorem certificate_proof_0409 (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ)
    (hh : ∀ j k, (a j).h k=h (facePair j k)) (ha : ∀ j, FaceResidue (a j))
    (hroot : h 0=0) : ∀ e, h e ≠ 1 := by
  have hstep (e : Fin 33) : h e=1 ↔ h (pairParent e)=1 := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    have hs := (ha (pairBridge e)).one_iff i k
    rw [hh,hh,hi,hk] at hs
    exact hs
  have hmain : ∀ m, ∀ e : Fin 33, e.val=m → h e≠1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro e hem he
      by_cases he0 : e=0
      · subst e; omega
      · have hp : (pairParent e).val < m := by simpa only [hem] using pairParent_lt e he0
        exact ih (pairParent e).val hp (pairParent e) rfl ((hstep e).mp he)
  intro e
  exact hmain e.val e rfl

private instance certificate_instance_0409 : OAI.SidorenkoCounterexample.ProofCertificate_0409 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0409 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0410 : ∃ D₀ : ℕ, ∀ D ≥ D₀,
    ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
    GlobalTailFeasible D full a h →
    (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0 →
    (∀ j, (a j).c=0) ∧ (∀ e, h e=0 ∨ h e=2) ∧
    (∀ j, tailSlack D (full j) (a j)=0) ∧ separationExcess h=0 ∧
    (∑ j, tailGain D (full j) (a j))=(2/3:ℝ)*∑ e, triangular (h e) := by
  obtain ⟨D₀,hD₀⟩ := eventually_integer_regime
  refine ⟨D₀,?_⟩
  intro D hD full a h ha htotal
  have hreg := hD₀ D hD full a h ha htotal
  have hn (j : Fin 22) : 0 ≤ tailSlack D (full j) (a j) := by
    cases hj : full j with
    | false => exact tailSlack_lower_nonneg (by simpa only [hj] using ha.1 j)
    | true => exact (integer_slack_classification (by simpa only [hj] using ha.1 j)
        (hreg j hj).1 (hreg j hj).2).1
  have hsn : 0 ≤ ∑ j, tailSlack D (full j) (a j) := Finset.sum_nonneg (fun j _ => hn j)
  have he : separationExcess h=0 := by linarith [separationExcess_nonneg h]
  have hsz : (∑ j, tailSlack D (full j) (a j))=0 := by linarith
  have hz (j : Fin 22) : tailSlack D (full j) (a j)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hsz j (Finset.mem_univ j)
  have hr (j : Fin 22) : FaceResidue (a j) := by
    cases hj : full j with
    | false => exact lower_zero_face_residue (by simpa only [hj] using ha.1 j) (by simpa only [hj] using hz j)
    | true =>
        exact full_zero_face_residue (by simpa only [hj] using ha.1 j)
          (hreg j hj).1 (hreg j hj).2 (by simpa only [hj] using hz j)
  have hnone := residue_propagation a h ha.2 hr (residue_root_zero h he)
  have hface (j : Fin 22) : (a j).c=0 ∧ ∀ k, (a j).h k=0 ∨ (a j).h k=2 := by
    rcases hr j with hh | ⟨_hc,hh⟩
    · exact hh
    · exact (hnone (facePair j 0) (by rw [←ha.2]; exact hh 0)).elim
  refine ⟨fun j => (hface j).1,?_,hz,he,?_⟩
  · intro e
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    have hh := (hface (pairBridge e)).2 k
    rwa [ha.2,hk] at hh
  · have hg (j : Fin 22) : tailGain D (full j) (a j)=
        (1/3:ℝ)*∑ k, triangular (h (facePair j k)) := by
      have hh := sub_eq_zero.mp (hz j)
      change faceBaseline D (a j).c (fun k => (a j).s k)=tailGain D (full j) (a j) at hh
      rw [←hh]
      have hk (k : Fin 3) : (a j).s k=h (facePair j k) := by
        have hk := ha.2 j k
        simpa only [TailTuple.h,(hface j).1,zero_add] using hk
      simp only [faceBaseline,(hface j).1,Nat.cast_zero,mul_zero,zero_add,hk]
      ring
    simp_rw [hg]
    rw [←Finset.mul_sum,sum_face_pairs (fun e => triangular (h e))]
    ring

private instance certificate_instance_0410 : OAI.SidorenkoCounterexample.ProofCertificate_0410 := by
  constructor
  exact @certificate_proof_0410 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0411 (D r c : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) (i : Fin 3) :
    (plantedTailTuple D r c s u θ).s i = s i := by
  have h := θ.property
  unfold BaseFeasible at h
  fin_cases i <;> simp [plantedTailTuple,TailTuple.s] <;> omega

private instance certificate_instance_0411 : OAI.SidorenkoCounterexample.ProofCertificate_0411 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0411 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0412 (D r c : ℕ) (hD : D=2*r) (hc : c ≤ D)
    (s : Fin 3 → ℕ) (hs : (∑ i, s i) ≤ D-c)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) :
    TailFeasible D true (plantedTailTuple D r c s u θ) := by
  have hu := u.property.1
  have huc : u.val.val ≤ c := Nat.le_of_lt_succ u.val.isLt
  have hθ := θ.property
  unfold BaseFeasible at hθ
  have hn : θ.val.2.2.2.val ≤ D-c := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hdc : ((D-c:ℕ):ℝ) = (D:ℝ)-c := Nat.cast_sub hc
  have hru : ((r-u.val.val:ℕ):ℝ) = (r:ℝ)-u.val.val := Nat.cast_sub hu
  have hDs : (D:ℝ)=2*r := by exact_mod_cast hD
  refine ⟨hc,?_,fun _ => ⟨huc,?_,?_,?_⟩⟩
  · change (∑ i, (plantedTailTuple D r c s u θ).s i) ≤ D-c
    simpa only [plantedTailTuple_s] using hs
  · intro i
    fin_cases i
    all_goals dsimp [plantedTailTuple,TailTuple.delta]
    · have hh := hθ.2.2.2.2.2.2.2.2.1
      have hh' : ((s 0-θ.val.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.1
      have hh' : ((s 1-θ.val.2.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((s 2-θ.val.2.2.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
  · intro i
    fin_cases i
    all_goals dsimp [plantedTailTuple,TailTuple.delta]
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
  · have hh := hθ.2.2.2.2.1
    have hh' : (θ.val.2.2.2.val:ℝ)+(θ.val.1.val+θ.val.2.1.val+θ.val.2.2.1.val) ≤ 3*(r-u.val.val:ℕ) := by exact_mod_cast hh
    rw [hru] at hh'
    simp only [plantedTailTuple,TailTuple.delta,TailTuple.P,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_sub hn,hdc]
    linarith

private instance certificate_instance_0412 : OAI.SidorenkoCounterexample.ProofCertificate_0412 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0412 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0413 (D c r : ℕ) (hD : D=2*r) (hc : c ≤ D)
    (s : Fin 3 → ℕ) (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) :
    fullPlantedExponent D c r s u θ = tailGain D true (plantedTailTuple D r c s u θ) := by
  have hu := u.property.1
  have huc : u.val.val ≤ c := Nat.le_of_lt_succ u.val.isLt
  have huD : u.val.val ≤ D := huc.trans hc
  have hθ := θ.property
  unfold BaseFeasible at hθ
  have hn : θ.val.2.2.2.val ≤ D-c := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hiso : (isotropicExponent D c:ℝ) + triangular (D-c:ℕ) = triangular D+(c:ℝ)*(D-c:ℕ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) (isotropicExponent_add D c hc)
    simpa only [Nat.cast_add,Nat.cast_mul,triangular_nat] using hh
  have hDs : (D:ℝ)=2*r := by exact_mod_cast hD
  have h0 : θ.val.1.val ≤ s 0 := hθ.2.2.2.2.2.1
  have h1 : θ.val.2.1.val ≤ s 1 := hθ.2.2.2.2.2.2.1
  have h2 : θ.val.2.2.1.val ≤ s 2 := hθ.2.2.2.2.2.2.2.1
  unfold fullPlantedExponent tailGain plantedGain plantedTailTuple TailTuple.delta reducedPlantedExponent
  simp only [ite_true,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_add,triangular_nat,Nat.cast_sub hn,Nat.cast_sub hc,
    Nat.cast_sub hu,Nat.cast_sub huc,Nat.cast_sub huD,Nat.cast_sub h0,Nat.cast_sub h1,Nat.cast_sub h2]
  rw [Nat.cast_sub hc] at hiso
  dsimp [triangular] at hiso ⊢
  rw [show (isotropicExponent D c:ℝ) = _ from (eq_sub_iff_add_eq.mpr hiso)]
  rw [hDs]
  ring

private instance certificate_instance_0413 : OAI.SidorenkoCounterexample.ProofCertificate_0413 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0413 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7

end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0414 {B : Type} [Finite B] {C : B → Type} [∀ b, Finite (C b)]
    (m : ℝ) (h : ∀ b, (Nat.card (C b) : ℝ) ≤ m) :
    (Nat.card (Σ b, C b) : ℝ) ≤ Nat.card B*m := by
  classical
  let := Fintype.ofFinite B
  let _ (b : B) := Fintype.ofFinite (C b)
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  calc
    (∑ b, (Fintype.card (C b):ℝ)) ≤ ∑ _b : B, m := Finset.sum_le_sum (fun b _ => by simpa only [Nat.card_eq_fintype_card] using h b)
    _ = (Fintype.card B:ℝ)*m := by simp

private instance certificate_instance_0414 : OAI.SidorenkoCounterexample.ProofCertificate_0414 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0414 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5

section PairDifference
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable (A B : Submodule K V)
theorem certificate_proof_0415 : Function.Surjective (pairFormDifference A B) := by
  intro F
  obtain ⟨G,hG⟩ := symFormPull_surjective
    (Submodule.inclusion inf_le_left : ↥(A ⊓ B) →ₗ[K] A) (Submodule.inclusion_injective _) F
  refine ⟨(G,0),?_⟩
  change symFormPull _ G-symFormPull _ 0=F
  rw [map_zero,sub_zero,hG]

private instance certificate_instance_0415 : OAI.SidorenkoCounterexample.ProofCertificate_0415 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0415 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0416 (F : SymForm K A) (G : SymForm K B) :
    (pairFormDifference A B (F,G)).val = graphDifference A B F.val G.val := rfl

private instance certificate_instance_0416 : OAI.SidorenkoCounterexample.ProofCertificate_0416 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0416 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0417 [Fintype K] [Finite V] (t : ℕ)
    (ht : t ≤ finrank K ↥(A ⊓ B)) :
    (Nat.card {FG : SymForm K A × SymForm K B //
      t ≤ finrank K (graphDifference A B FG.1.val FG.2.val).ker} : ℝ) /
        Nat.card (SymForm K A × SymForm K B) ≤
      2^t/(Fintype.card K : ℝ)^((t+1).choose 2) := by
  change (Nat.card {FG : SymForm K A × SymForm K B //
      t ≤ finrank K (pairFormDifference A B FG).val.ker} : ℝ) / _ ≤ _
  rw [surjective_linear_probability (pairFormDifference A B) (pairFormDifference_surjective A B) (fun F => t ≤ finrank K F.val.ker)]
  exact symmetric_nullity_probability_bound t ht

private instance certificate_instance_0417 : OAI.SidorenkoCounterexample.ProofCertificate_0417 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0417 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end PairDifference
section PairBaseCounts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0418 (r p : ℕ) :
    Function.Injective (pairBaseCode (K := K) (V := V) (r := r) (p := p)) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun c : PairBaseCode (K := K) (V := V) r p => (c.1,c.2.2.val)) h

private instance certificate_instance_0418 : OAI.SidorenkoCounterexample.ProofCertificate_0418 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0418 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6

variable [Fintype K] [Finite V]
theorem certificate_proof_0419 (r p : ℕ) (hr : r ≤ finrank K V) (hp : p ≤ r) :
    (Nat.card (SubspacePairProfile (K := K) (V := V) r p) : ℝ) ≤
      (2^r*(Fintype.card K : ℝ)^(r*(finrank K V-r))) *
        ((2^p*(Fintype.card K : ℝ)^(p*(r-p))) *
          (2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r)))) := by
  have hq : (0:ℝ) ≤ Fintype.card K := by positivity
  have hP (R : DimSubspace K V r) (P : DimSubspace K R.val p) :
      (Nat.card {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val} : ℝ) ≤
        2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r)) := by
    have hd : finrank K (P.val.map R.val.subtype) = p :=
      (Submodule.finrank_map_subtype_eq R.val P.val).trans P.property
    have hh := (containingSubspace_card_bounds (P.val.map R.val.subtype) r (by rwa [hd]) hr).2
    rwa [hd] at hh
  have hR (R : DimSubspace K V r) :
      (Nat.card (Σ P : DimSubspace K R.val p,
        {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val}) : ℝ) ≤
        (2^p*(Fintype.card K : ℝ)^(p*(r-p))) *
          (2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r))) := by
    refine (real_card_sigma_le _ (hP R)).trans ?_
    have hc := subspace_count_upper (K := K) (V := R.val) p (by rwa [R.property])
    rw [R.property] at hc
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hc : (Nat.card (SubspacePairProfile (K := K) (V := V) r p) : ℝ) ≤
      Nat.card (PairBaseCode (K := K) (V := V) r p) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pairBaseCode_injective (K := K) (V := V) r p)
  refine (hc.trans (real_card_sigma_le _ hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (subspace_count_upper r hr) (by positivity)

private instance certificate_instance_0419 : OAI.SidorenkoCounterexample.ProofCertificate_0419 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0419 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0420 (r p : ℕ) (hD : finrank K V = 2*r) (hp : p ≤ r) :
    (Fintype.card K : ℝ)^(p*p) * Nat.card (SubspacePairProfile (K := K) (V := V) r p) ≤
      2^(2*r+p)*(Nat.card (DimSubspace K V r):ℝ)^2 := by
  have hr : r ≤ finrank K V := by omega
  have hc := subspacePairProfile_card_upper (K := K) (V := V) r p hr hp
  rw [hD,show 2*r-r=r by omega] at hc
  have hl := subspace_count_lower (K := K) (V := V) r hr
  rw [hD,show 2*r-r=r by omega] at hl
  have hexp : p*p+r*r+(p*(r-p)+(r-p)*r)=2*(r*r) := by
    have hs := Nat.sub_add_cancel hp
    nlinarith
  have htwo : r+(p+r)=2*r+p := by omega
  let q : ℝ := Fintype.card K
  calc
    q^(p*p)*Nat.card (SubspacePairProfile (K := K) (V := V) r p) ≤
        q^(p*p)*((2^r*q^(r*r))*((2^p*q^(p*(r-p)))*(2^r*q^((r-p)*r)))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2^(2*r+p)*(q^(r*r))^2 := by
      rw [show q^(p*p)*((2^r*q^(r*r))*((2^p*q^(p*(r-p)))*(2^r*q^((r-p)*r)))) =
        (2^r*(2^p*2^r))*(q^(p*p)*q^(r*r)*(q^(p*(r-p))*q^((r-p)*r))) by ring]
      rw [←pow_add,←pow_add,htwo,←pow_add,←pow_add,←pow_add,hexp,pow_mul]
      rw [pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hl 2) (by positivity)

private instance certificate_instance_0420 : OAI.SidorenkoCounterexample.ProofCertificate_0420 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0420 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end PairBaseCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PairLiftCounts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0421 (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) =
      finrank K ↥(R ⊓ S)+finrank K (graphDifference _ _ F.val G.val).ker := by
  have hh := graph_pair_intersection_finrank R.dualCoannihilator S.dualCoannihilator F.val G.val
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq (W := R),
    Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)] at hh
  exact hh

private instance certificate_instance_0421 : OAI.SidorenkoCounterexample.ProofCertificate_0421 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0421 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

variable [Fintype K] [Finite V]
end PairLiftCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section PairFinal
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
end PairFinal
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SymplecticPairPlanted
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end SymplecticPairPlanted
section PairPointwise
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end PairPointwise
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ActualProfile
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0391 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0392 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0393 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0394 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0395 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0396 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0397 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0398 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0399 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0400 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0401 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0402 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0403 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0404 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0405 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0406 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0407 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0408 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0409 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0410 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0411 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0412 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0413 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0414 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0415 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0416 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0417 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0418 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0419 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0420 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0421 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

