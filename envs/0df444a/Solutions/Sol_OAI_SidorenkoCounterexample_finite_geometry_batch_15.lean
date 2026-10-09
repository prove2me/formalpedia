-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_15
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:17:59.910967+00:00
-- url     : https://prove2.me/submissions/5372ce0c-860e-4c6e-81ea-37f947ce5c9e

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0339]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0340]
include p0 p1

namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0341 (c d δ v : ℝ) (p t : Fin 3 → ℝ)
    (hc : |δ| ≤ c) (hd : (∑ i, p i)+(∑ i, t i) ≤ d)
    (hp : ∀ i, 0 ≤ p i) (ht : ∀ i, 0 ≤ t i) (hv : 0 ≤ v)
    (htp : ∀ i, t i ≤ p i+δ) (hvp : ∀ i, v ≤ p i+δ)
    (hw : 0 ≤ (d-3*δ)/2-(∑ i, p i)+v) :
    ((∑ i, p i)^2+(∑ i, t i)^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤
      quadraticPart c d δ v p t := by
  let P := ∑ i, p i
  let T := ∑ i, t i
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => hp i
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => ht i
  have hTP : T ≤ P+3*δ := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => htp i)
    simpa [Finset.sum_add_distrib, P, T] using hh
  have hvP : v ≤ P/3+δ := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hvp i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hh
    change (3:ℝ)*v ≤ P+3*δ at hh
    linarith only [hh]
  let m := min (P/3+δ) ((P-T+3*δ)/2)
  let k := (d-3*δ)/2-P
  have hm : 0 ≤ m := le_min (by linarith only [hv, hvP]) (by linarith only [hTP])
  have hkm : -k ≤ m := by
    apply le_min
    · dsimp [k]
      change 0 ≤ (d-3*δ)/2-P+v at hw
      linarith only [hw, hvP]
    · dsimp [k]
      change P+T ≤ d at hd
      linarith only [hd]
  have hvquad : -m^2/2 ≤ k*v+v^2/2 := by
    by_cases hk : 0 ≤ k
    · nlinarith only [mul_nonneg hk hv, sq_nonneg v, sq_nonneg m]
    · have hh₁ : 0 ≤ m+k := by linarith only [hkm]
      have hh₂ : 0 ≤ m-k := by linarith only [hm, hk]
      nlinarith only [mul_nonneg hh₁ hh₂, sq_nonneg (v+k)]
  have hsq := three_sq (fun i => 2*p i-t i)
  have hsum : (∑ i, (2*p i-t i)) = 2*P-T := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum, P, T]
  rw [hsum] at hsq
  have hscalar := coercivity_scalar c d P T δ hc hd hP hT hTP
  change (P^2+T^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤ _
  calc
    _ ≤ scalarForm c d P T δ := hscalar
    _ ≤ quadraticPart c d δ v p t := by
      dsimp [scalarForm, quadraticPart]
      change _ ≤ (c*(d+δ)-δ*d+2*δ^2)/4 + (∑ i, (2*p i-t i)^2)/6 +
        δ*P-c*(P+T)/6+k*v+v^2/2
      change - (min (P/3+δ) ((P-T+3*δ)/2))^2/2 ≤ _ at hvquad
      nlinarith only [hsq, hvquad]

private instance certificate_instance_0341 : OAI.SidorenkoCounterexample.ProofCertificate_0341 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0341 p0 p1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0342 (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    (c*(d+δ-1)-δ*(d+2)+2*δ^2)/4 +
    (∑ i, ((2*p i-t i)*(2*p i-t i-1)/6 + δ*p i-c*(p i+t i)/6)) +
    v*((d-3*δ)/2-(∑ i, p i)+v) - triangular v := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring

private instance certificate_instance_0342 : OAI.SidorenkoCounterexample.ProofCertificate_0342 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0342 p0 p1 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0343 (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    quadraticPart c d δ v p t - c/4 - δ/2 -
      (2*(∑ i, p i)-(∑ i, t i))/6-v/2 := by
  rw [slack_identity]
  simp only [quadraticPart, triangular, Fin.sum_univ_three]
  ring

private instance certificate_instance_0343 : OAI.SidorenkoCounterexample.ProofCertificate_0343 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0343 p0 p1 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0344 (c d δ v M : ℝ) (p t : Fin 3 → ℝ)
    (hc : 0 ≤ c) (hδ : δ ≤ c) (hv : v ≤ M)
    (hP : (∑ i, p i) ≤ 3*(M-c)) (hT : 0 ≤ ∑ i, t i) :
    quadraticPart c d δ v p t - 3*M/2 ≤
      baseline c d p t - plantedGain c d δ v p t := by
  rw [slack_quadratic]
  linarith only [hc, hδ, hv, hP, hT]

private instance certificate_instance_0344 : OAI.SidorenkoCounterexample.ProofCertificate_0344 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0344 p0 p1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0345 (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    ((c-δ+2*v)/4)*d + baseline c 0 p t - plantedGain c 0 δ v p t := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring

private instance certificate_instance_0345 : OAI.SidorenkoCounterexample.ProofCertificate_0345 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0345 p0 p1 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0346 (c d : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d c 0 p t =
    (3*c^2-3*c)/4 +
      (∑ i, ((2*p i-t i)^2+(c-1)*(2*p i-t i)+3*c*p i))/6 := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring

private instance certificate_instance_0346 : OAI.SidorenkoCounterexample.ProofCertificate_0346 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0346 p0 p1 q0 q1 q2 q3

theorem certificate_proof_0347 (c d : ℝ) (p t : Fin 3 → ℝ)
    (hc : 2 ≤ c) (hp : ∀ i, 0 ≤ p i) :
    0 < baseline c d p t - plantedGain c d c 0 p t := by
  rw [slack_integer_regime]
  have hi (i : Fin 3) : -(c-1)^2/4 ≤
      (2*p i-t i)^2+(c-1)*(2*p i-t i)+3*c*p i := by
    have hh := mul_nonneg (show 0 ≤ c by linarith) (hp i)
    nlinarith only [hh, sq_nonneg (2*p i-t i+(c-1)/2)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hpos : 0 < (c-1)*(5*c+1) := mul_pos (by linarith) (by linarith)
  nlinarith only [hh, hpos]

private instance certificate_instance_0347 : OAI.SidorenkoCounterexample.ProofCertificate_0347 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0347 p0 p1 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0348 (p t : ℤ) (hp : 0 ≤ p) (ht : 0 ≤ t) (htp : t ≤ p) :
    0 ≤ (2*p-t)*(2*p-t-1) ∧
      ((2*p-t)*(2*p-t-1) = 0 ↔ (p=0 ∧ t=0) ∨ (p=1 ∧ t=1)) := by
  have hn : 0 ≤ 2*p-t := by omega
  constructor
  · by_cases hz : 2*p-t = 0
    · simp [hz]
    · exact mul_nonneg hn (by omega)
  · rw [mul_eq_zero]
    constructor
    · intro h
      rcases h with h | h
      · left; omega
      · right; omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

private instance certificate_instance_0348 : OAI.SidorenkoCounterexample.ProofCertificate_0348 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0348 p0 p1 q0 q1 q2 q3 q4

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0349 {x : ℝ} (hx : 0 ≤ x) : 0 ≤ triangular x := by
  unfold triangular; positivity

private instance certificate_instance_0349 : OAI.SidorenkoCounterexample.ProofCertificate_0349 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0349 p0 p1 q0 q1

theorem certificate_proof_0350 {x : ℝ} (hx : 0 < x) : 0 < triangular x := by
  unfold triangular; positivity

private instance certificate_instance_0350 : OAI.SidorenkoCounterexample.ProofCertificate_0350 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0350 p0 p1 q0 q1

theorem certificate_proof_0351 {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    triangular x ≤ triangular y := by
  have h := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ y+x+1 by linarith)
  dsimp [triangular]; nlinarith only [h]

private instance certificate_instance_0351 : OAI.SidorenkoCounterexample.ProofCertificate_0351 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0351 p0 p1 q0 q1 q2 q3

theorem certificate_proof_0352 (n : ℕ) : ((n+1).choose 2 : ℝ) = triangular n := by
  rw [Nat.cast_choose_two]
  simp only [Nat.cast_add,Nat.cast_one]
  unfold triangular
  ring

private instance certificate_instance_0352 : OAI.SidorenkoCounterexample.ProofCertificate_0352 := by
  constructor
  intro q0
  exact @certificate_proof_0352 p0 p1 q0

theorem certificate_proof_0353 (D c : ℝ) (s : Fin 3 → ℝ) (k : Fin 3)
    (hc : 0 ≤ c) (hs : ∀ i, 0 ≤ s i) (hD : (∑ i, s i) ≤ D-c) :
    triangular (c+s k)/3 + triangular c/6 +
      ((∑ i, triangular (s i))-triangular (s k))/3 ≤ faceBaseline D c s := by
  have hm : s k ≤ ∑ i, s i := Finset.single_le_sum (fun i _ => hs i) (Finset.mem_univ k)
  have hn := mul_nonneg hc (show 0 ≤ 3*(D-c)-(∑ i, s i)-2*s k by linarith)
  have he : faceBaseline D c s - (triangular (c+s k)/3 + triangular c/6 +
      ((∑ i, triangular (s i))-triangular (s k))/3) =
      c*(3*(D-c)-(∑ i, s i)-2*s k)/6 := by
    simp only [faceBaseline,triangular,Fin.sum_univ_three]
    ring
  linarith only [hn,he]

private instance certificate_instance_0353 : OAI.SidorenkoCounterexample.ProofCertificate_0353 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0353 p0 p1 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0354 (h : ℕ) :
    0 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
    (h:ℝ)^2/24-(h:ℝ)/12 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
    (triangular (h:ℝ)/3-triangular (h/2:ℕ) = 0 ↔ h=0 ∨ h=2) := by
  have hd := Nat.mod_add_div h 2
  have hr := Nat.mod_lt h (by norm_num : 0<2)
  have hq : 0 ≤ (h/2:ℕ) := Nat.zero_le _
  have hqr : (0:ℝ) ≤ (h/2:ℕ) := Nat.cast_nonneg _
  rcases (show h%2=0 ∨ h%2=1 by omega) with he | he
  · have hh : h=2*(h/2) := by omega
    have hh' : (h:ℝ)=2*(h/2:ℕ) := by exact_mod_cast hh
    have hn : (h/2:ℕ)=0 ∨ (h/2:ℕ)=1 ∨ 2 ≤ h/2 := by omega
    rcases hn with hn | hn | hn
    · have hz : h=0 := by omega
      subst h; norm_num [triangular]
    · have hz : h=2 := by omega
      subst h; norm_num [triangular]
    · have hn' : (2:ℝ) ≤ (h/2:ℕ) := by exact_mod_cast hn
      have hp : 0 < (h/2:ℕ)*( (h/2:ℕ)-1 : ℝ) := mul_pos (by linarith) (by linarith)
      dsimp [triangular]
      constructor
      · nlinarith only [hh',hp]
      constructor
      · nlinarith only [hh',sq_nonneg ((h/2:ℕ):ℝ)]
      constructor
      · intro hz; nlinarith only [hh',hp,hz]
      · intro hz; rcases hz with hz | hz <;> omega
  · have hh : h=2*(h/2)+1 := by omega
    have hh' : (h:ℝ)=2*(h/2:ℕ)+1 := by exact_mod_cast hh
    have hp : 0 < ((h/2:ℕ):ℝ)+1 := by positivity
    have hp' := mul_pos hp (show (0:ℝ) < (h/2:ℕ)+2 by positivity)
    dsimp [triangular]
    constructor
    · nlinarith only [hh',hp',sq_nonneg ((h/2:ℕ):ℝ)]
    constructor
    · nlinarith only [hh',sq_nonneg ((h/2:ℕ):ℝ),hqr]
    constructor
    · intro hz; nlinarith only [hh',hp',hz]
    · intro hz; rcases hz with hz | hz <;> omega

private instance certificate_instance_0354 : OAI.SidorenkoCounterexample.ProofCertificate_0354 := by
  constructor
  intro q0
  exact @certificate_proof_0354 p0 p1 q0

theorem certificate_proof_0355 (D c : ℕ) (s : Fin 3 → ℕ) (k : Fin 3) (g : ℝ)
    (hD : (∑ i, s i) ≤ D-c) (hcD : c ≤ D)
    (_hk : ∀ i, s i ≤ s k) (hg : g ≤ triangular ((c+s k)/2:ℕ)) :
    0 ≤ faceBaseline D c (fun i => s i)-g ∧
    ((c+s k:ℕ):ℝ)^2/24-((c+s k:ℕ):ℝ)/12 ≤ faceBaseline D c (fun i => s i)-g ∧
    (faceBaseline D c (fun i => s i)-g = 0 →
      c=0 ∧ (∀ i, i≠k → s i=0) ∧ (s k=0 ∨ s k=2)) := by
  have hD' : (∑ i, (s i:ℝ)) ≤ (D:ℝ)-c := by exact_mod_cast hD
  have hb := faceBaseline_lower (D:ℝ) c (fun i => s i) k (by positivity) (fun i => by positivity) hD'
  have hh := half_triangular_bounds (c+s k)
  have he : 0 ≤ (∑ i, triangular (s i))-triangular (s k) := by
    exact sub_nonneg.mpr (Finset.single_le_sum (fun i _ => triangular_nonneg (Nat.cast_nonneg _)) (Finset.mem_univ k))
  have hct : 0 ≤ triangular (c:ℝ) := triangular_nonneg (Nat.cast_nonneg _)
  simp only [Nat.cast_add] at hh
  refine ⟨by linarith [hh.1],by simp only [Nat.cast_add]; linarith [hh.2.1],?_⟩
  intro hz
  have hc : c=0 := by
    by_contra hc
    have hp := triangular_pos (show (0:ℝ)<c by exact_mod_cast Nat.pos_of_ne_zero hc)
    linarith [hh.1]
  subst c
  simp only [Nat.cast_zero,zero_add] at hb hh hg hz
  have hothers : (∑ i, triangular (s i))-triangular (s k) = 0 := by
    have hz0 : triangular (0:ℝ)=0 := by norm_num [triangular]
    rw [hz0] at hb
    linarith [hh.1]
  refine ⟨rfl,?_,?_⟩
  · intro i hik
    have hle : triangular (s i)+triangular (s k) ≤ ∑ j, triangular (s j) := by
      have hsub : ({i,k}:Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
      have hx := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => triangular_nonneg (Nat.cast_nonneg (s j)))
      simpa only [Finset.sum_pair hik] using hx
    have hi0 : triangular (s i)=0 := by linarith [triangular_nonneg (Nat.cast_nonneg (s i))]
    by_contra hi
    have hp := triangular_pos (show (0:ℝ)<s i by exact_mod_cast Nat.pos_of_ne_zero hi)
    linarith
  · apply (half_triangular_bounds (s k)).2.2.mp
    have hz0 : triangular (0:ℝ)=0 := by norm_num [triangular]
    rw [hz0] at hb
    linarith [(half_triangular_bounds (s k)).1]

private instance certificate_instance_0355 : OAI.SidorenkoCounterexample.ProofCertificate_0355 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0355 p0 p1 q0 q1 q2 q3 q4 q5 q6 q7 q8

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0356 (a : TailTuple) (i : Fin 3) : a.h i ≤ a.maxH :=
  Finset.le_sup (Finset.mem_univ i)

private instance certificate_instance_0356 : OAI.SidorenkoCounterexample.ProofCertificate_0356 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0356 p0 p1 q0 q1

theorem certificate_proof_0357 (a : TailTuple) : ∃ i, a.maxH=a.h i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty a.h
  exact ⟨i,hi⟩

private instance certificate_instance_0357 : OAI.SidorenkoCounterexample.ProofCertificate_0357 := by
  constructor
  intro q0
  exact @certificate_proof_0357 p0 p1 q0

theorem certificate_proof_0358 (a : TailTuple) : a.c ≤ a.maxH :=
  (Nat.le_add_right a.c (a.s 0)).trans (a.h_le_max 0)

private instance certificate_instance_0358 : OAI.SidorenkoCounterexample.ProofCertificate_0358 := by
  constructor
  intro q0
  exact @certificate_proof_0358 p0 p1 q0

theorem certificate_proof_0359 (a : TailTuple) (i : Fin 3) : a.p i ≤ a.h i := by
  unfold TailTuple.h TailTuple.s; omega

private instance certificate_instance_0359 : OAI.SidorenkoCounterexample.ProofCertificate_0359 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0359 p0 p1 q0 q1

theorem certificate_proof_0360 (a : TailTuple) (i : Fin 3) : a.t i ≤ a.h i := by
  unfold TailTuple.h TailTuple.s; omega

private instance certificate_instance_0360 : OAI.SidorenkoCounterexample.ProofCertificate_0360 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0360 p0 p1 q0 q1

theorem certificate_proof_0361 (a : TailTuple) (i : Fin 3) : a.s i ≤ a.h i := by
  unfold TailTuple.h; omega

private instance certificate_instance_0361 : OAI.SidorenkoCounterexample.ProofCertificate_0361 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0361 p0 p1 q0 q1

theorem certificate_proof_0362 (a : TailTuple) (hu : a.u ≤ a.c) : |a.delta| ≤ (a.c:ℝ) := by
  have hu' : (a.u:ℝ) ≤ a.c := by exact_mod_cast hu
  rw [abs_le]
  dsimp [TailTuple.delta]
  constructor <;> linarith [(Nat.cast_nonneg a.u : (0:ℝ) ≤ a.u)]

private instance certificate_instance_0362 : OAI.SidorenkoCounterexample.ProofCertificate_0362 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0362 p0 p1 q0 q1

theorem certificate_proof_0363 (D : ℕ) (a : TailTuple) :
    faceBaseline D a.c (fun i => a.s i) =
      baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i) := by
  simp only [faceBaseline,SidorenkoCounterexample.baseline,TailTuple.s,Nat.cast_add,sub_add_cancel,add_assoc]

private instance certificate_instance_0363 : OAI.SidorenkoCounterexample.ProofCertificate_0363 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0363 p0 p1 q0 q1

theorem certificate_proof_0364 {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : TailFeasible D full a) : a.P+a.T ≤ (D:ℝ)-a.c := by
  have hh : (∑ i, (a.s i:ℝ)) ≤ (D:ℝ)-a.c := by
    have hc : ((D-a.c:ℕ):ℝ) = (D:ℝ)-a.c := Nat.cast_sub ha.1
    rw [←hc,←Nat.cast_sum]
    exact_mod_cast ha.2.1
  simpa only [TailTuple.s,Nat.cast_add,Finset.sum_add_distrib,TailTuple.P,TailTuple.T] using hh

private instance certificate_instance_0364 : OAI.SidorenkoCounterexample.ProofCertificate_0364 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0364 p0 p1 q0 q1 q2 q3

theorem certificate_proof_0365 {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) : 0 ≤ (D:ℝ)-a.c+3*a.delta := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (ha.2.2 rfl).2.1 i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at ht
  change a.T ≤ a.P+3*a.delta at ht
  have hT : 0 ≤ a.T := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  linarith [ha.sum_le]

private instance certificate_instance_0365 : OAI.SidorenkoCounterexample.ProofCertificate_0365 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0365 p0 p1 q0 q1 q2

theorem certificate_proof_0366 {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) :
    0 ≤ a.energy D ∧ (a.P^2+a.T^2+a.delta^2)/342 ≤ a.energy D := by
  have h := mul_nonneg (sub_nonneg.mpr (a.delta_abs_le (ha.2.2 rfl).1)) ha.d_delta_nonneg
  dsimp [TailTuple.energy]
  constructor
  · positivity
  · linarith only [h]

private instance certificate_instance_0366 : OAI.SidorenkoCounterexample.ProofCertificate_0366 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0366 p0 p1 q0 q1 q2

theorem certificate_proof_0367 {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) : a.energy D ≤ a.Q D := by
  apply SidorenkoCounterexample.coercivity
  · exact a.delta_abs_le (ha.2.2 rfl).1
  · exact ha.sum_le
  · intro i; positivity
  · intro i; positivity
  · positivity
  · exact (ha.2.2 rfl).2.1
  · exact (ha.2.2 rfl).2.2.1
  · exact (ha.2.2 rfl).2.2.2

private instance certificate_instance_0367 : OAI.SidorenkoCounterexample.ProofCertificate_0367 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0367 p0 p1 q0 q1 q2

theorem certificate_proof_0368 {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) : a.v ≤ a.maxH := by
  have hv := (ha.2.2 rfl).2.2.1 0
  have hδ := le_abs_self a.delta |>.trans (a.delta_abs_le (ha.2.2 rfl).1)
  have hp : (a.p 0:ℝ) ≤ a.h 0-a.c := by
    dsimp [TailTuple.h,TailTuple.s]; push_cast; linarith [(Nat.cast_nonneg (a.t 0) : (0:ℝ) ≤ a.t 0)]
  have hh : (a.h 0:ℝ) ≤ a.maxH := by exact_mod_cast a.h_le_max 0
  have hv' : (a.v:ℝ) ≤ a.maxH := by linarith
  exact_mod_cast hv'

private instance certificate_instance_0368 : OAI.SidorenkoCounterexample.ProofCertificate_0368 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0368 p0 p1 q0 q1 q2

theorem certificate_proof_0369 {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : TailFeasible D full a) : 0 ≤ tailEnergy D full a := by
  cases full
  · simp only [tailEnergy,Bool.false_eq_true,ite_false]; positivity
  · exact ha.energy_nonneg.1

private instance certificate_instance_0369 : OAI.SidorenkoCounterexample.ProofCertificate_0369 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0369 p0 p1 q0 q1 q2 q3

theorem certificate_proof_0370 {D : ℕ} {full : Bool} {a : TailTuple} (M : ℝ)
    (ha : TailFeasible D full a) (hM : (a.maxH:ℝ) ≤ M) :
    tailEnergy D full a-3*M/2 ≤ tailSlack D full a := by
  cases full
  · obtain ⟨k,hk⟩ := a.exists_max
    have hsk (i : Fin 3) : a.s i ≤ a.s k := by
      have hh := a.h_le_max i
      rw [hk] at hh
      exact Nat.le_of_add_le_add_left hh
    have hh := lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
      (by rw [hk]; rfl)
    simp only [tailSlack,tailGain,tailEnergy,Bool.false_eq_true,ite_false]
    rw [hk] at hh ⊢
    have hhM : (a.c+a.s k:ℕ) ≤ M := by simpa only [hk,TailTuple.h] using hM
    have hMn : 0 ≤ M := (Nat.cast_nonneg a.maxH).trans hM
    change ((a.c+a.s k:ℕ):ℝ)^2/24-3*M/2 ≤ _
    linarith [hh.2.1]
  · have hc : (a.c:ℝ) ≤ M := le_trans (by exact_mod_cast a.c_le_max) hM
    have hv : (a.v:ℝ) ≤ M := le_trans (by exact_mod_cast ha.v_le_max) hM
    have hP : a.P ≤ 3*(M-a.c) := by
      have hi (i : Fin 3) : (a.p i:ℝ) ≤ M-a.c := by
        have hh : (a.h i:ℝ) ≤ M := le_trans (by exact_mod_cast a.h_le_max i) hM
        dsimp [TailTuple.h,TailTuple.s] at hh
        push_cast at hh
        linarith [(Nat.cast_nonneg (a.t i) : (0:ℝ) ≤ a.t i)]
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
      simpa only [TailTuple.P,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hh
    have hδ : a.delta ≤ (a.c:ℝ) := (le_abs_self _).trans (a.delta_abs_le (ha.2.2 rfl).1)
    have hh := slack_uniform_linear (a.c:ℝ) ((D:ℝ)-a.c) a.delta (a.v:ℝ) M
      (fun i => (a.p i:ℝ)) (fun i => (a.t i:ℝ)) (by positivity) hδ hv hP
      (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
    have hh' := sub_le_sub_right ha.coercivity (3*M/2)
    simpa only [tailSlack,tailGain,tailEnergy,ite_true,a.baseline D,TailTuple.Q] using hh'.trans hh

private instance certificate_instance_0370 : OAI.SidorenkoCounterexample.ProofCertificate_0370 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0370 p0 p1 q0 q1 q2 q3 q4 q5

end SidorenkoCounterexample
namespace SidorenkoCounterexample
theorem certificate_proof_0371 : ∀ j, (faces j).card = 3 := by decide

private instance certificate_instance_0371 : OAI.SidorenkoCounterexample.ProofCertificate_0371 := by
  constructor
  intro q0
  exact @certificate_proof_0371 p0 p1 q0

theorem certificate_proof_0372 : ∀ e, (pairVertices e).card = 2 := by decide

private instance certificate_instance_0372 : OAI.SidorenkoCounterexample.ProofCertificate_0372 := by
  constructor
  intro q0
  exact @certificate_proof_0372 p0 p1 q0

theorem certificate_proof_0373 : Function.Injective pairVertices := by decide

private instance certificate_instance_0373 : OAI.SidorenkoCounterexample.ProofCertificate_0373 := by
  constructor
  exact @certificate_proof_0373 p0 p1

theorem certificate_proof_0374 : ∀ j, Function.Injective (facePair j) := by decide

private instance certificate_instance_0374 : OAI.SidorenkoCounterexample.ProofCertificate_0374 := by
  constructor
  intro q0
  exact @certificate_proof_0374 p0 p1 q0

theorem certificate_proof_0375 : ∀ j e, pairVertices e ⊆ faces j ↔ ∃ k, facePair j k=e := by decide

private instance certificate_instance_0375 : OAI.SidorenkoCounterexample.ProofCertificate_0375 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0375 p0 p1 q0 q1

theorem certificate_proof_0376 : ∀ e j, pairVertices e ⊆ faces j ↔ ∃ k, pairFace e k=j := by decide

private instance certificate_instance_0376 : OAI.SidorenkoCounterexample.ProofCertificate_0376 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0376 p0 p1 q0 q1

theorem certificate_proof_0377 : ∀ e, Function.Injective (pairFace e) := by decide

private instance certificate_instance_0377 : OAI.SidorenkoCounterexample.ProofCertificate_0377 := by
  constructor
  intro q0
  exact @certificate_proof_0377 p0 p1 q0

theorem certificate_proof_0378 : ∀ e, e≠0 → (pairParent e).val < e.val := by decide

private instance certificate_instance_0378 : OAI.SidorenkoCounterexample.ProofCertificate_0378 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0378 p0 p1 q0 q1

theorem certificate_proof_0379 : ∀ e, pairVertices e ⊆ faces (pairBridge e) := by decide

private instance certificate_instance_0379 : OAI.SidorenkoCounterexample.ProofCertificate_0379 := by
  constructor
  intro q0
  exact @certificate_proof_0379 p0 p1 q0

theorem certificate_proof_0380 : ∀ e, pairVertices (pairParent e) ⊆ faces (pairBridge e) := by decide

private instance certificate_instance_0380 : OAI.SidorenkoCounterexample.ProofCertificate_0380 := by
  constructor
  intro q0
  exact @certificate_proof_0380 p0 p1 q0

theorem certificate_proof_0381 : ∀ e, 1 ≤ separationCount e := by decide

private instance certificate_instance_0381 : OAI.SidorenkoCounterexample.ProofCertificate_0381 := by
  constructor
  intro q0
  exact @certificate_proof_0381 p0 p1 q0

theorem certificate_proof_0382 : separationCount 0=3 := by decide

private instance certificate_instance_0382 : OAI.SidorenkoCounterexample.ProofCertificate_0382 := by
  constructor
  exact @certificate_proof_0382 p0 p1

theorem certificate_proof_0383 : ∀ e, separationCount e ≤ 3 := by decide

private instance certificate_instance_0383 : OAI.SidorenkoCounterexample.ProofCertificate_0383 := by
  constructor
  intro q0
  exact @certificate_proof_0383 p0 p1 q0

theorem certificate_proof_0384 : pairVertices 0={0,2} := by rfl

private instance certificate_instance_0384 : OAI.SidorenkoCounterexample.ProofCertificate_0384 := by
  constructor
  exact @certificate_proof_0384 p0 p1

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0385 (a b M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M) (hbM : b ≤ M) : (a-b)^2 ≤ M^2 := by
  have hM : 0 ≤ M := ha.trans haM
  have hab : |a-b| ≤ M := abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (sq_le_sq₀ (abs_nonneg _) hM).2 hab
  simpa only [sq_abs] using hh

private instance certificate_instance_0385 : OAI.SidorenkoCounterexample.ProofCertificate_0385 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0385 p0 p1 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0386 {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : TailFeasible D full a) (i k : Fin 3) :
    ((a.h i:ℝ)-a.h k)^2 ≤ 684*tailEnergy D full a := by
  cases full
  · have hm (j : Fin 3) : (a.h j:ℝ) ≤ a.maxH := by exact_mod_cast a.h_le_max j
    have hh := nonnegative_interval_sq (a.h i) (a.h k) a.maxH (by positivity) (by positivity) (hm i) (hm k)
    simp only [tailEnergy,Bool.false_eq_true,ite_false]
    nlinarith [sq_nonneg (a.maxH:ℝ)]
  · have hs (j : Fin 3) : (a.s j:ℝ) ≤ a.P+a.T := by
      have hh : (a.s j:ℝ) ≤ ∑ k, (a.s k:ℝ) :=
        Finset.single_le_sum (fun k _ => Nat.cast_nonneg (a.s k)) (Finset.mem_univ j)
      simpa only [TailTuple.s,Nat.cast_add,Finset.sum_add_distrib,TailTuple.P,TailTuple.T] using hh
    have hh := nonnegative_interval_sq (a.s i) (a.s k) (a.P+a.T) (by positivity) (by positivity) (hs i) (hs k)
    have he := ha.energy_nonneg.2
    simp only [tailEnergy,ite_true]
    simp only [TailTuple.h,Nat.cast_add]
    nlinarith only [hh,he,sq_nonneg (a.P-a.T),sq_nonneg a.delta]

private instance certificate_instance_0386 : OAI.SidorenkoCounterexample.ProofCertificate_0386 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0386 p0 p1 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0387 {n : ℕ} (p : Fin (n+1) → Fin (n+1))
    (hp : ∀ i, i≠0 → (p i).val < i.val) (f : Fin (n+1) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hstep : ∀ i, (f i-f (p i))^2 ≤ K) (i : Fin (n+1)) :
    (f i-f 0)^2 ≤ (4:ℝ)^i.val*K := by
  have hmain : ∀ m, ∀ i : Fin (n+1), i.val=m → (f i-f 0)^2 ≤ (4:ℝ)^i.val*K := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him
      by_cases hi : i=0
      · subst i; simpa using hK
      · have hpm : (p i).val < m := by simpa only [him] using hp i hi
        have hind := ih (p i).val hpm (p i) rfl
        have hpow : (4:ℝ)^((p i).val+1) ≤ (4:ℝ)^i.val :=
          pow_le_pow_right₀ (by norm_num) (hp i hi)
        have hone : (1:ℝ) ≤ (4:ℝ)^(p i).val := one_le_pow₀ (by norm_num)
        have hc := mul_le_mul_of_nonneg_right hpow hK
        have hk' := mul_le_mul_of_nonneg_right hone hK
        rw [pow_succ] at hc
        have hh := hstep i
        nlinarith only [hind,hc,hk',hh,sq_nonneg ((f i-f (p i))-(f (p i)-f 0))]
  exact hmain i.val i rfl

private instance certificate_instance_0387 : OAI.SidorenkoCounterexample.ProofCertificate_0387 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0387 p0 p1 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0388 (h : Fin 33 → ℕ) : 0 ≤ separationExcess h := by
  apply Finset.sum_nonneg
  intro e _
  have he : (1:ℝ) ≤ separationCount e := by exact_mod_cast separationCount_pos e
  exact mul_nonneg (by linarith) (triangular_nonneg (Nat.cast_nonneg _))

private instance certificate_instance_0388 : OAI.SidorenkoCounterexample.ProofCertificate_0388 := by
  constructor
  intro q0
  exact @certificate_proof_0388 p0 p1 q0

theorem certificate_proof_0389 (h : Fin 33 → ℕ) :
    (h 0:ℝ)^2/6 ≤ separationExcess h := by
  have hn (e : Fin 33) : 0 ≤ ((separationCount e:ℝ)-1)/6*triangular (h e) := by
    have hh : (1:ℝ) ≤ separationCount e := by exact_mod_cast separationCount_pos e
    exact mul_nonneg (by linarith) (triangular_nonneg (Nat.cast_nonneg _))
  have he : ((separationCount 0:ℝ)-1)/6*triangular (h 0) ≤ separationExcess h :=
    Finset.single_le_sum (fun e _ => hn e) (Finset.mem_univ (0 : Fin 33))
  rw [separationCount_root] at he
  norm_num only [Nat.cast_ofNat] at he
  dsimp [triangular] at he
  nlinarith [(Nat.cast_nonneg (h 0) : (0:ℝ) ≤ h 0)]

private instance certificate_instance_0389 : OAI.SidorenkoCounterexample.ProofCertificate_0389 := by
  constructor
  intro q0
  exact @certificate_proof_0389 p0 p1 q0

theorem certificate_proof_0390 (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0) :
    (∑ j, tailEnergy D (full j) (a j))+separationExcess h ≤
      33*((Finset.univ.sup h:ℕ):ℝ) := by
  let M : ℝ := (Finset.univ.sup h:ℕ)
  have hM (j : Fin 22) : ((a j).maxH:ℝ) ≤ M := by
    have hh : (a j).maxH ≤ Finset.univ.sup h := by
      apply Finset.sup_le
      intro k _
      rw [ha.2 j k]
      exact Finset.le_sup (Finset.mem_univ _)
    change ((a j).maxH:ℝ) ≤ ((Finset.univ.sup h:ℕ):ℝ)
    exact_mod_cast hh
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun j _ => tailSlack_energy_lower M (ha.1 j) (hM j))
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  change (∑ j, tailEnergy D (full j) (a j))-22*(3*M/2) ≤ _ at hi
  change (∑ j, tailEnergy D (full j) (a j))+separationExcess h ≤ 33*M
  linarith only [hi,htotal]

private instance certificate_instance_0390 : OAI.SidorenkoCounterexample.ProofCertificate_0390 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0390 p0 p1 q0 q1 q2 q3 q4 q5

end SidorenkoCounterexample
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
open scoped BigOperators
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0341 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0342 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0343 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0344 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0345 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0346 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0347 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0348 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0349 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0350 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0351 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0352 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0353 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0354 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0355 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0356 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0357 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0358 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0359 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0360 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0361 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0362 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0363 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0364 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0365 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0366 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0367 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0368 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0369 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0370 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0371 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0372 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0373 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0374 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0375 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0376 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0377 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0378 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0379 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0380 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0381 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0382 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0383 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0384 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0385 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0386 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0387 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0388 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0389 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0390 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

