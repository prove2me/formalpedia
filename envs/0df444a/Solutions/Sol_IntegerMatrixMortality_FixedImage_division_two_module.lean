-- Prove2me | solution 1 for IntegerMatrixMortality.FixedImage.division_two_module
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:35:53.652671+00:00
-- url     : https://prove2.me/submissions/7bb478a5-68eb-499d-9056-fbbed2322cd3

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IMMSol
open IntegerMatrixMortality.FixedImage

lemma la_formula (p : ℕ) (hp : (p:ℚ) ≠ 0) (q r : ℕ) (d : ℤ) (pre : ℕ → ℤ) (neg : Bool)
    (post : ℕ → ℤ) (z : ℚ)
    (h1 : (p:ℚ) * pre p * z + 1 ≠ 0)
    (h2 : (p:ℚ) * post p * ((z / ((p:ℚ) * pre p * z + 1) - d) / p) + 1 ≠ 0) :
    localAction p (GE q r d pre neg post) (some z) =
      some ((if neg then -1 else 1) * ((z / (p * pre p * z + 1) - d) / p) /
        (p * post p * ((z / (p * pre p * z + 1) - d) / p) + 1)) := by
  set w := (z / ((p:ℚ) * pre p * z + 1) - d) / p with hw
  have ew : w * (p * (p * pre p * z + 1)) = z - d * (p * pre p * z + 1) := by
    have h1' : z * p * pre p + 1 ≠ 0 := by rwa [show z * p * pre p = p * pre p * z by ring]
    rw [hw]; field_simp
  simp only [localAction, localMatrix, GE, auxiliaryMatrix, deletionMatrix, rationalMatrix,
    projectiveAction]
  simp
  have hDne : ∀ D : ℚ, D = (↑p * ↑(post p) + (-(↑p * ↑(post p) * ↑d) + ↑p) * (↑p * ↑(pre p))) * z + (-(↑p * ↑(post p) * ↑d) + ↑p) → D ≠ 0 := by
    intro D hD h0
    apply mul_ne_zero (mul_ne_zero hp h1) h2
    linear_combination h0 - hD + (p * post p : ℚ) * ew
  refine ⟨hDne _ rfl, ?_⟩
  rw [div_eq_div_iff (hDne _ rfl) h2]
  cases neg
  · simp
    linear_combination (-1 : ℚ) * ew
  · simp
    linear_combination ew

lemma la_plain (p : ℕ) (hp : (p:ℚ) ≠ 0) (q r : ℕ) (d : ℤ) (z : ℚ) :
    localAction p (GE q r d) (some z) = some ((z - d) / p) := by
  rw [la_formula p hp q r d _ _ _ z (by simp) (by simp)]; simp

lemma la_pre (p : ℕ) (hp : (p:ℚ) ≠ 0) (q r : ℕ) (d : ℤ) (g : ℕ → ℤ) (z : ℚ)
    (h1 : (p:ℚ) * g p * z + 1 ≠ 0) :
    localAction p (GE q r d g) (some z) = some ((z / (p * g p * z + 1) - d) / p) := by
  rw [la_formula p hp q r d _ _ _ z h1 (by simp)]; simp

def pt (p m N : ℕ) : ℚ := (p:ℚ)^m / (1 - (p:ℚ)^N)

section
variable {p : ℕ}

lemma one_sub_pow_ne (hp : p.Prime) {N : ℕ} (hN : 1 ≤ N) : (1 - (p:ℚ)^N) ≠ 0 := by
  have h2 : (2:ℚ) ≤ p := by exact_mod_cast hp.two_le
  have : (2:ℚ) ≤ (p:ℚ)^N := le_trans h2 (le_self_pow₀ (by linarith) (by omega))
  intro h; linarith

lemma not_dvd_one (hp : p.Prime) : ¬ (p:ℤ) ∣ 1 := by
  intro h
  have := Int.eq_one_of_dvd_one (by positivity) h
  exact hp.one_lt.ne' (by exact_mod_cast this)

lemma not_dvd_one_sub (hp : p.Prime) {N : ℕ} (hN : 1 ≤ N) : ¬ (p:ℤ) ∣ 1 - (p:ℤ)^N := by
  intro h
  have h2 : (p:ℤ) ∣ (p:ℤ)^N := dvd_pow_self _ (by omega)
  exact not_dvd_one hp (by simpa using dvd_add h h2)

lemma valid_of_eq (hp : p.Prime) (x : ℚ) (a b : ℤ) (hb : ¬ (p:ℤ) ∣ b) (hx : x = a / b) :
    Valid p (some x) := by
  simp only [Valid]
  intro h
  apply hb
  have : (x.den : ℤ) ∣ b := by
    have := Rat.den_dvd a b
    rwa [Rat.divInt_eq_div, ← hx] at this
  exact dvd_trans h this

lemma num_mul_eq (x : ℚ) (a b : ℤ) (hb : (b:ℚ) ≠ 0) (hx : x = a / b) :
    x.num * b = a * x.den := by
  have hden : (x.den : ℚ) ≠ 0 := by positivity
  have h : (x.num : ℚ) / x.den = a / b := by rw [Rat.num_div_den, hx]
  rw [div_eq_div_iff hden hb] at h
  exact_mod_cast h

lemma not_valid_of_eq (hp : p.Prime) (x : ℚ) (a b : ℤ) (ha : ¬ (p:ℤ) ∣ a) (hb : (b:ℚ) ≠ 0)
    (hx : x = a / (p * b)) : ¬ Valid p (some x) := by
  simp only [Valid, not_not]
  by_contra hd
  have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 := num_mul_eq x a (p * b) (by push_cast; exact mul_ne_zero hp0 hb) (by push_cast; exact hx)
  have : (p:ℤ) ∣ a * x.den := ⟨x.num * b, by rw [← h2]; ring⟩
  rcases hpz.dvd_or_dvd this with h | h
  · exact ha h
  · exact hd h

lemma hasResidue_of_eq (hp : p.Prime) (x : ℚ) (a b e : ℤ) (hb : ¬ (p:ℤ) ∣ b)
    (hx : x = a / b) (hr : (p:ℤ) ∣ a - e * b) : HasResidue p (some x) e := by
  refine ⟨x, rfl, valid_of_eq hp x a b hb hx, ?_⟩
  have hb0 : (b:ℚ) ≠ 0 := by
    intro h; apply hb; have : b = 0 := by exact_mod_cast h
    rw [this]; exact dvd_zero _
  have h2 := num_mul_eq x a b hb0 hx
  have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (p:ℤ) ∣ (x.num - e * x.den) * b := by
    have : (x.num - e * x.den) * b = x.den * (a - e * b) := by linear_combination h2
    rw [this]; exact dvd_mul_of_dvd_right hr _
  rcases hpz.dvd_or_dvd this with h | h
  · exact h
  · exact absurd h hb

lemma valid_pt (hp : p.Prime) (m : ℕ) {N : ℕ} (hN : 1 ≤ N) : Valid p (some (pt p m N)) :=
  valid_of_eq hp _ ((p:ℤ)^m) (1 - (p:ℤ)^N) (not_dvd_one_sub hp hN) (by simp [pt])

lemma inRes_pt (hp : p.Prime) (m : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    InResidues p (some (pt p m N)) delta := by
  rcases m with _ | m
  · refine ⟨1, by simp [delta], hasResidue_of_eq hp _ 1 (1 - (p:ℤ)^N) 1
      (not_dvd_one_sub hp hN) (by simp [pt]) ?_⟩
    rw [show (1:ℤ) - 1 * (1 - (p:ℤ)^N) = (p:ℤ)^N by ring]; exact dvd_pow_self _ (by omega)
  · refine ⟨0, by simp [delta], hasResidue_of_eq hp _ ((p:ℤ)^(m+1)) (1 - (p:ℤ)^N) 0
      (not_dvd_one_sub hp hN) (by simp [pt]) ?_⟩
    rw [show (p:ℤ)^(m+1) - 0 * (1 - (p:ℤ)^N) = (p:ℤ)^(m+1) by ring]
    exact dvd_pow_self _ (by omega)

lemma del0_succ (hp : p.Prime) (m N : ℕ) : (pt p (m+1) N - ((0:ℤ):ℚ)) / p = pt p m N := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp [pt]; field_simp; ring

lemma del0_zero_invalid (hp : p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    ¬ Valid p (some ((pt p 0 N - ((0:ℤ):ℚ)) / p)) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb := one_sub_pow_ne hp hN
  refine not_valid_of_eq hp _ 1 (1 - (p:ℤ)^N) (not_dvd_one hp) (by push_cast; exact hb) ?_
  simp [pt]; field_simp

lemma del1_zero (hp : p.Prime) (M : ℕ) : (pt p 0 (M+1) - ((1:ℤ):ℚ)) / p = pt p M (M+1) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb := one_sub_pow_ne hp (N := M+1) (by omega)
  simp [pt]; field_simp; ring

lemma del1_zero' (hp : p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    (pt p 0 N - ((1:ℤ):ℚ)) / p = pt p (N-1) N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [del1_zero hp M]; simp

lemma del1_succ_invalid (hp : p.Prime) (m : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ¬ Valid p (some ((pt p (m+1) N - ((1:ℤ):ℚ)) / p)) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb := one_sub_pow_ne hp hN
  refine not_valid_of_eq hp _ ((p:ℤ)^(m+1) - 1 + (p:ℤ)^N) (1 - (p:ℤ)^N) ?_
    (by push_cast; exact hb) ?_
  · intro h
    have h1 : (p:ℤ) ∣ (p:ℤ)^(m+1) := dvd_pow_self _ (by omega)
    have h2 : (p:ℤ) ∣ (p:ℤ)^N := dvd_pow_self _ (by omega)
    apply not_dvd_one hp
    have := dvd_sub (dvd_sub h1 h) h2
    have e : (p:ℤ)^(m+1) - ((p:ℤ)^(m+1) - 1 + (p:ℤ)^N) - (p:ℤ)^N = 1 - 2 * (p:ℤ)^N := by ring
    rw [e] at this
    have := dvd_add this (dvd_mul_of_dvd_right h2 2)
    simpa using this
  · simp [pt]; field_simp; ring

end

lemma valid_start {p : ℕ} {edges : List GeneratorEdge} {q : ℕ} {x : ProjectivePoint}
    {w : List GeneratorEdge} {r : ℕ} {y : ProjectivePoint}
    (h : ValidWalk p edges q x w r y) : Valid p x := by
  cases h <;> assumption

lemma walk_inv {p : ℕ} {edges : List GeneratorEdge} (Inv : ℕ → ProjectivePoint → Prop)
    (hstep : ∀ q x e, Inv q x → e ∈ edges → e.source = q → Valid p x →
      Valid p (localAction p e x) → Inv e.target (localAction p e x))
    {q : ℕ} {x : ProjectivePoint} {w : List GeneratorEdge} {r : ℕ} {y : ProjectivePoint}
    (h : ValidWalk p edges q x w r y) : Inv q x → Inv r y := by
  induction h with
  | nil => exact id
  | cons q r x y e es he hq hx tail ih =>
    intro hI; exact ih (hstep q x e hI he hq hx (valid_start tail))

lemma walk_cons {p : ℕ} {edges : List GeneratorEdge} {q : ℕ} {x x' : ProjectivePoint}
    (e : GeneratorEdge) {es : List GeneratorEdge} {r : ℕ} {y : ProjectivePoint}
    (he : e ∈ edges) (hq : e.source = q) (hx : Valid p x) (hx' : localAction p e x = x')
    (tail : ValidWalk p edges e.target x' es r y) : ValidWalk p edges q x (e :: es) r y :=
  ValidWalk.cons q r x y e es he hq hx (hx' ▸ tail)

lemma firstArrival_append (l : List GeneratorEdge) (b : GeneratorEdge) (r : ℕ)
    (h : ∀ e ∈ l, e.target ≠ r) : FirstArrival (l ++ [b]) r := by
  intro i hi
  have hil : i < l.length := by simp at hi; omega
  rw [List.getElem?_append_left hil, List.getElem?_eq_getElem hil]
  simp only [Option.map_some, ne_eq, Option.some.injEq]
  exact h _ (List.getElem_mem _)

lemma computable_one_sub : Computable (fun p : ℕ => 1 - (p : ℤ)) := by
  have hg : Primrec (fun n : ℕ => if n = 0 then 2 else if n = 1 then 0 else 2 * n - 3) := by
    refine Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 2) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 0) ?_
    exact Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 3)
  have := ((Primrec.ofNat ℤ).comp hg).to_comp
  refine this.of_eq ?_
  intro n
  rw [← Denumerable.ofNat_encode (1 - (n:ℤ))]
  congr 1
  rcases n with _ | _ | n
  · rfl
  · rfl
  · simp only [show 1 - ((n + 1 + 1 : ℕ) : ℤ) = Int.negSucc n by push_cast; omega]
    show _ = Equiv.intEquivNat (Int.negSucc n)
    simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat]
    omega

end IMMSol

namespace IMMSol
open IntegerMatrixMortality.FixedImage

lemma la_gen (p : ℕ) (hp : (p:ℚ) ≠ 0) (q r : ℕ) (d : ℤ) (neg : Bool) (post : ℕ → ℤ) (z : ℚ) :
    localAction p (GE q r d (fun _ => 0) neg post) (some z) =
      if (p:ℚ) * post p * ((z - d) / p) + 1 = 0 then none else
      some ((if neg then -1 else 1) * ((z - d) / p) / (p * post p * ((z - d) / p) + 1)) := by
  by_cases h2 : (p:ℚ) * post p * ((z - d) / p) + 1 = 0
  · rw [if_pos h2]
    simp only [localAction, localMatrix, GE, auxiliaryMatrix, deletionMatrix, rationalMatrix,
      projectiveAction]
    simp
    have e : (p:ℚ) * post p * ((z - d) / p) = post p * (z - d) := by field_simp
    rw [e] at h2; linear_combination (p:ℚ) * h2
  · rw [if_neg h2, la_formula p hp q r d _ _ _ z (by simp) (by simpa using h2)]
    cases neg <;> simp

section
variable {p : ℕ}

lemma nd_of (hp7 : 7 ≤ p) {X : ℤ} (r : ℤ) (hr0 : r ≠ 0) (hr1 : -7 < r) (hr2 : r < 7)
    (h : (p:ℤ) ∣ X - r) : ¬ (p:ℤ) ∣ X := by
  intro hX
  have h' : (p:ℤ) ∣ r := by have := dvd_sub hX h; rwa [sub_sub_cancel] at this
  have h2 := Int.natAbs_dvd_natAbs.mpr h'
  simp only [Int.natAbs_natCast] at h2
  have h1 : (p:ℤ) ≤ (r.natAbs : ℤ) := by exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.mpr hr0) h2
  rw [Int.natCast_natAbs] at h1
  have : |r| < 7 := abs_lt.mpr ⟨by linarith, hr2⟩
  have : (7:ℤ) ≤ p := by exact_mod_cast hp7
  linarith

lemma nb_of (hp : p.Prime) {B : ℤ} (hB : (p:ℤ) ∣ B - 1) : ¬ (p:ℤ) ∣ B := by
  intro h; apply not_dvd_one hp
  have := dvd_sub h hB; rwa [sub_sub_cancel] at this

lemma Bne (hp : p.Prime) {B : ℤ} (hB : (p:ℤ) ∣ B - 1) : (B:ℚ) ≠ 0 := by
  intro h; apply nb_of hp hB; have : B = 0 := by exact_mod_cast h
  rw [this]; exact dvd_zero _

lemma valid_frac (hp : p.Prime) (x : ℚ) (A B : ℤ) (hB : (p:ℤ) ∣ B - 1) (hx : x = A / B) :
    Valid p (some x) := valid_of_eq hp x A B (nb_of hp hB) hx

lemma inres_frac (hp : p.Prime) (x : ℚ) (A B e : ℤ) (he : e ∈ delta) (hB : (p:ℤ) ∣ B - 1)
    (hx : x = A / B) (hA : (p:ℤ) ∣ A - e) : InResidues p (some x) delta := by
  refine ⟨e, he, hasResidue_of_eq hp x A B e (nb_of hp hB) hx ?_⟩
  have : A - e * B = (A - e) - e * (B - 1) := by ring
  rw [this]; exact dvd_sub hA (dvd_mul_of_dvd_right hB _)

lemma del_invalid (hp : p.Prime) (z : ℚ) (A B e : ℤ) (hB : (p:ℤ) ∣ B - 1) (hz : z = A / B)
    (hA : ¬ (p:ℤ) ∣ A - e) : ¬ Valid p (some ((z - e) / p)) := by
  have hB0 := Bne hp hB
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine not_valid_of_eq hp _ (A - e * B) B ?_ hB0 ?_
  · intro h; apply hA
    have : A - e = (A - e * B) + e * (B - 1) := by ring
    rw [this]; exact dvd_add h (dvd_mul_of_dvd_right hB _)
  · rw [hz]; push_cast; field_simp

lemma post_inv_valid (hp : p.Prime) (S : ℤ) (hS : S * S = 1) (h : ℤ) (w : ℚ)
    (hden : (p:ℚ) * h * w + 1 ≠ 0) (hv : Valid p (some ((S:ℚ) * w / (p * h * w + 1)))) :
    Valid p (some w) := by
  set y := (S:ℚ) * w / (p * h * w + 1) with hydef
  have hb : ¬ (p:ℤ) ∣ (y.den : ℤ) := hv
  have hy : y * (p * h * w + 1) = S * w := by rw [hydef, div_mul_cancel₀ _ hden]
  have hyab : y = (y.num : ℚ) / (y.den : ℚ) := (Rat.num_div_den y).symm
  have hden0 : (y.den : ℚ) ≠ 0 := by positivity
  have nd : ¬ (p:ℤ) ∣ S * y.den - p * h * y.num := by
    intro hd; apply hb
    have h1 : (p:ℤ) ∣ S * y.den := by
      have := dvd_add hd (dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) h) y.num)
      simpa using this
    have := dvd_mul_of_dvd_right h1 S
    rwa [← mul_assoc, hS, one_mul] at this
  have hne : ((S * y.den - p * h * y.num : ℤ) : ℚ) ≠ 0 := by
    intro h0; apply nd; have : S * (y.den:ℤ) - p * h * y.num = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  refine valid_of_eq hp w y.num (S * y.den - p * h * y.num) nd ?_
  rw [eq_div_iff hne]
  have hS' : (S:ℚ) * S = 1 := by exact_mod_cast hS
  rw [hyab] at hy
  field_simp at hy
  push_cast
  linear_combination (-1:ℚ) * hy

lemma post_step (hp : p.Prime) (q r : ℕ) (d : ℤ) (neg : Bool) (post : ℕ → ℤ) (z : ℚ)
    (hv : Valid p (localAction p (GE q r d (fun _ => 0) neg post) (some z))) :
    Valid p (some ((z - d) / p)) ∧
    localAction p (GE q r d (fun _ => 0) neg post) (some z) =
      some ((if neg then -1 else 1) * ((z - d) / p) / (p * post p * ((z - d) / p) + 1)) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [la_gen p hp0] at hv ⊢
  by_cases h2 : (p:ℚ) * post p * ((z - d) / p) + 1 = 0
  · rw [if_pos h2] at hv; exact absurd hv (by simp [Valid])
  · rw [if_neg h2] at hv ⊢
    refine ⟨?_, rfl⟩
    cases neg
    · exact post_inv_valid hp 1 (by norm_num) _ _ h2 (by convert hv using 3; simp)
    · exact post_inv_valid hp (-1) (by norm_num) _ _ h2 (by convert hv using 3; simp)

end

end IMMSol

namespace IMMSol
open IntegerMatrixMortality.FixedImage

section
variable {p : ℕ}

lemma del_eq (hp0 : (p:ℚ) ≠ 0) (A B e A' : ℚ) (hB : B ≠ 0) (h : A - e * B = p * A') :
    (A / B - e) / p = A' / B := by
  field_simp; linear_combination h

lemma post_eval (hp0 : (p:ℚ) ≠ 0) (S h A B e A' : ℚ) (hB : B ≠ 0) (hdel : A - e * B = p * A')
    (hC : B + p * h * A' ≠ 0) :
    S * ((A / B - e) / p) / (p * h * ((A / B - e) / p) + 1) = S * A' / (B + p * h * A') := by
  rw [del_eq hp0 A B e A' hB hdel]
  rw [show (p:ℚ) * h * (A' / B) + 1 = (B + p * h * A') / B by field_simp; ring]
  field_simp

lemma la_post_eval (hp0 : (p:ℚ) ≠ 0) (q r : ℕ) (d : ℤ) (neg : Bool) (post : ℕ → ℤ)
    (A B A' : ℚ) (hB : B ≠ 0) (hdel : A - d * B = p * A')
    (hC : B + p * post p * A' ≠ 0) :
    localAction p (GE q r d (fun _ => 0) neg post) (some (A / B)) =
      some ((if neg then -1 else 1) * A' / (B + p * post p * A')) := by
  rw [la_gen p hp0, if_neg, post_eval hp0 _ _ A B d A' hB hdel hC]
  rw [del_eq hp0 A B d A' hB hdel]
  rw [show (p:ℚ) * post p * (A' / B) + 1 = (B + p * post p * A') / B by field_simp; ring]
  exact div_ne_zero hC hB

lemma la_plain_eval (hp0 : (p:ℚ) ≠ 0) (q r : ℕ) (d : ℤ) (A B A' : ℚ) (hB : B ≠ 0)
    (hdel : A - d * B = p * A') :
    localAction p (GE q r d) (some (A / B)) = some (A' / B) := by
  rw [la_plain p hp0, del_eq hp0 A B d A' hB hdel]

lemma hDne (hp : p.Prime) (a N : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    (1 - (p:ℚ)^a - (p:ℚ)^N) ≠ 0 := by
  have h1 : (1:ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
  have : (1:ℚ) ≤ (p:ℚ)^a := one_le_pow₀ h1
  have : (1:ℚ) ≤ (p:ℚ)^N := one_le_pow₀ h1
  intro h; linarith

lemma hDdvd (a N : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    (p:ℤ) ∣ (1 - (p:ℤ)^a - (p:ℤ)^N) - 1 := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  exact ⟨-((p:ℤ)^a + (p:ℤ)^N), by ring⟩

lemma hEdvd (b : ℕ) (hb : 1 ≤ b) : (p:ℤ) ∣ (1 + (p:ℤ)^b) - 1 := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  exact ⟨(p:ℤ)^b, by ring⟩

lemma hEne (b : ℕ) : (1 + (p:ℚ)^b) ≠ 0 := by positivity

lemma valid_start' {edges : List GeneratorEdge} {q : ℕ} {x : ProjectivePoint}
    {w : List GeneratorEdge} {r : ℕ} {y : ProjectivePoint}
    (h : ValidWalk p edges q x w r y) : Valid p y := by
  induction h with
  | nil _ _ h => exact h
  | cons _ _ _ _ _ _ _ _ _ _ ih => exact ih

lemma walk_append {edges : List GeneratorEdge} {q : ℕ} {x : ProjectivePoint}
    {w1 : List GeneratorEdge} {r : ℕ} {y : ProjectivePoint} {w2 : List GeneratorEdge} {s : ℕ}
    {z : ProjectivePoint}
    (h1 : ValidWalk p edges q x w1 r y) (h2 : ValidWalk p edges r y w2 s z) :
    ValidWalk p edges q x (w1 ++ w2) s z := by
  induction h1 with
  | nil _ _ _ => exact h2
  | cons q r x y e es he hq hx tail ih => exact ValidWalk.cons _ _ _ _ _ _ he hq hx (ih h2)

lemma loop_walk {edges : List GeneratorEdge} (e : GeneratorEdge) (he : e ∈ edges) (s : ℕ)
    (hs : e.source = s) (ht : e.target = s) (F : ℕ → ℚ) (hv : ∀ j, Valid p (some (F j)))
    (hstep : ∀ j, localAction p e (some (F (j+1))) = some (F j)) :
    ∀ j, ValidWalk p edges s (some (F j)) (List.replicate j e) s (some (F 0)) := by
  intro j
  induction j with
  | zero => exact ValidWalk.nil _ _ (hv 0)
  | succ j ih =>
    refine walk_cons e he hs (hv _) (hstep j) ?_
    rw [ht]; exact ih

end

lemma div2_edges : div2Module.edges = [GE 0 2 0, GE 0 3 0 (fun _ => 0) false (fun _ => -1),
    GE 2 2 0, GE 2 3 0 (fun _ => 0) false (fun _ => -1),
    GE 3 3 0, GE 3 4 1, GE 4 4 0, GE 4 5 1 (fun _ => 0) false (fun _ => 1),
    GE 5 5 0, GE 5 1 2 (fun _ => 0) true (fun _ => 2)] := rfl

end IMMSol

namespace IMMSol
open IntegerMatrixMortality.FixedImage

def D2Inv (p n : ℕ) : ℕ → ProjectivePoint → Prop
  | 0, x => x = some (pt p n (n+1))
  | 1, x => ∃ a, n = 2*a+1 ∧ x = some (pt p a (a+1))
  | 2, x => ∃ c, c < n ∧ x = some (pt p c (n+1))
  | 3, x => ∃ c j, c < n ∧ x = some ((p:ℚ)^j / (1 - (p:ℚ)^(c+1) - (p:ℚ)^(n+1)))
  | 4, x => ∃ c b i, n = c + b ∧ 1 ≤ b ∧
      x = some (((p:ℚ)^i + (p:ℚ)^(i+b)) / (1 - (p:ℚ)^(c+1) - (p:ℚ)^(n+1)))
  | 5, x => ∃ b u v, 1 ≤ b ∧ u + n + 1 = v + 2*b ∧
      x = some (((p:ℚ)^u + (p:ℚ)^v + (p:ℚ)^(v+b)) / (1 + (p:ℚ)^b))
  | _, _ => False

lemma d2_step (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : ∀ q x e, D2Inv p n q x →
    e ∈ div2Module.edges → e.source = q → Valid p x → Valid p (localAction p e x) →
    D2Inv p n e.target (localAction p e x) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro q x e hI he hq hx hv
  rw [div2_edges] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [GE] at hq <;> subst hq <;> simp only [D2Inv] at hI
  · -- E1 : 0 → 2, delete 0
    subst hI
    rw [la_plain p hp0] at hv ⊢
    show D2Inv p n 2 _
    simp only [D2Inv]
    rcases n with _ | m
    · exact absurd hv (del0_zero_invalid hp (by norm_num))
    · rw [del0_succ hp]; exact ⟨m, by omega, rfl⟩
  · -- E2 : 0 → 3, delete 0 then T
    subst hI
    obtain ⟨hw, heq⟩ := post_step hp 0 3 0 false (fun _ => -1) _ hv
    rw [heq]; show D2Inv p n 3 _; simp only [D2Inv]
    rcases n with _ | m
    · exact absurd hw (del0_zero_invalid hp (by norm_num))
    · refine ⟨m, m, by omega, ?_⟩
      congr 1
      have hB := one_sub_pow_ne hp (N := m+1+1) (by omega)
      refine (post_eval hp0 1 ((-1:ℤ):ℚ) _ _ _ ((p:ℚ)^m) hB (by push_cast; ring) ?_).trans ?_
      · rw [show (1 - (p:ℚ)^(m+1+1)) + p * ((-1:ℤ):ℚ) * (p:ℚ)^m
          = 1 - (p:ℚ)^(m+1) - (p:ℚ)^(m+1+1) by push_cast; ring]
        exact hDne hp _ _ (by omega) (by omega)
      · push_cast; ring
  · -- E3 : 2 → 2
    obtain ⟨c, hc, rfl⟩ := hI
    rw [la_plain p hp0] at hv ⊢
    show D2Inv p n 2 _
    simp only [D2Inv]
    rcases c with _ | c
    · exact absurd hv (del0_zero_invalid hp (by omega))
    · rw [del0_succ hp]; exact ⟨c, by omega, rfl⟩
  · -- E4 : 2 → 3, T
    obtain ⟨c, hc, rfl⟩ := hI
    obtain ⟨hw, heq⟩ := post_step hp 2 3 0 false (fun _ => -1) _ hv
    rw [heq]; show D2Inv p n 3 _; simp only [D2Inv]
    rcases c with _ | c
    · exact absurd hw (del0_zero_invalid hp (by omega))
    · refine ⟨c, c, by omega, ?_⟩
      congr 1
      have hB := one_sub_pow_ne hp (N := n+1) (by omega)
      refine (post_eval hp0 1 ((-1:ℤ):ℚ) _ _ _ ((p:ℚ)^c) hB (by push_cast; ring) ?_).trans ?_
      · rw [show (1 - (p:ℚ)^(n+1)) + p * ((-1:ℤ):ℚ) * (p:ℚ)^c
          = 1 - (p:ℚ)^(c+1) - (p:ℚ)^(n+1) by push_cast; ring]
        exact hDne hp _ _ (by omega) (by omega)
      · push_cast; ring
  · -- E5 : 3 → 3, delete 0
    obtain ⟨c, j, hc, rfl⟩ := hI
    have hB := hDne hp (c+1) (n+1) (by omega) (by omega)
    rw [la_plain p hp0] at hv ⊢
    show D2Inv p n 3 _
    simp only [D2Inv]
    rcases j with _ | j
    · exact absurd hv (del_invalid hp _ 1 (1 - (p:ℤ)^(c+1) - (p:ℤ)^(n+1)) 0
        (hDdvd _ _ (by omega) (by omega)) (by push_cast; ring) (by simpa using not_dvd_one hp))
    · exact ⟨c, j, hc, by rw [del_eq hp0 _ _ _ ((p:ℚ)^j) hB (by push_cast; ring)]⟩
  · -- E6 : 3 → 4, delete 1
    obtain ⟨c, j, hc, rfl⟩ := hI
    have hB := hDne hp (c+1) (n+1) (by omega) (by omega)
    rw [la_plain p hp0] at hv ⊢
    show D2Inv p n 4 _
    simp only [D2Inv]
    rcases j with _ | j
    · obtain ⟨b, rfl⟩ : ∃ b, n = c + (b + 1) := ⟨n - c - 1, by omega⟩
      refine ⟨c, b+1, c, rfl, by omega, ?_⟩
      rw [del_eq hp0 _ _ _ ((p:ℚ)^c + (p:ℚ)^(c+(b+1))) hB (by push_cast; ring)]
    · exact absurd hv (del_invalid hp _ ((p:ℤ)^(j+1)) (1 - (p:ℤ)^(c+1) - (p:ℤ)^(n+1)) 1
        (hDdvd _ _ (by omega) (by omega)) (by push_cast; ring)
        (nd_of hp7 (-1) (by norm_num) (by norm_num) (by norm_num) ⟨(p:ℤ)^j, by ring⟩))
  · -- E7 : 4 → 4, delete 0
    obtain ⟨c, b, i, hn, hb, rfl⟩ := hI
    have hB := hDne hp (c+1) (n+1) (by omega) (by omega)
    rw [la_plain p hp0] at hv ⊢
    show D2Inv p n 4 _
    simp only [D2Inv]
    rcases i with _ | i
    · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      exact absurd hv (del_invalid hp _ (1 + (p:ℤ)^(b+1)) (1 - (p:ℤ)^(c+1) - (p:ℤ)^(n+1)) 0
        (hDdvd _ _ (by omega) (by omega)) (by push_cast; ring)
        (nd_of hp7 1 (by norm_num) (by norm_num) (by norm_num) ⟨(p:ℤ)^b, by ring⟩))
    · refine ⟨c, b, i, hn, hb, ?_⟩
      rw [del_eq hp0 _ _ _ ((p:ℚ)^i + (p:ℚ)^(i+b)) hB (by push_cast; ring)]
  · -- E8 : 4 → 5, delete 1 then T⁻¹
    obtain ⟨c, b, i, hn, hb, rfl⟩ := hI
    have hB := hDne hp (c+1) (n+1) (by omega) (by omega)
    obtain ⟨hw, heq⟩ := post_step hp 4 5 1 false (fun _ => 1) _ hv
    rw [heq]; show D2Inv p n 5 _; simp only [D2Inv]
    rcases i with _ | i
    · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      subst hn
      refine ⟨b+1, b, c, by omega, by omega, ?_⟩
      congr 1
      refine (post_eval hp0 1 ((1:ℤ):ℚ) _ _ _ ((p:ℚ)^b + (p:ℚ)^c + (p:ℚ)^(c+(b+1))) hB
        (by push_cast; ring) ?_).trans ?_
      · rw [show (1 - (p:ℚ)^(c+1) - (p:ℚ)^(c + (b+1) + 1)) + p * ((1:ℤ):ℚ) *
            ((p:ℚ)^b + (p:ℚ)^c + (p:ℚ)^(c+(b+1))) = 1 + (p:ℚ)^(b+1) by push_cast; ring]
        exact hEne _
      · push_cast; ring
    · exact absurd hw (del_invalid hp _ ((p:ℤ)^(i+1) + (p:ℤ)^(i+1+b))
        (1 - (p:ℤ)^(c+1) - (p:ℤ)^(n+1)) 1
        (hDdvd _ _ (by omega) (by omega)) (by push_cast; ring)
        (nd_of hp7 (-1) (by norm_num) (by norm_num) (by norm_num) ⟨(p:ℤ)^i + (p:ℤ)^(i+b), by ring⟩))
  · -- E9 : 5 → 5, delete 0
    obtain ⟨b, u, v, hb, hc, rfl⟩ := hI
    have hB := hEne (p := p) b
    have hBd := hEdvd (p := p) b hb
    rw [la_plain p hp0] at hv ⊢
    show D2Inv p n 5 _
    simp only [D2Inv]
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rcases u with _ | u <;> rcases v with _ | v
    · exact absurd hv (del_invalid hp _ (1 + 1 + (p:ℤ)^(0+(b+1))) (1 + (p:ℤ)^(b+1)) 0
        hBd (by push_cast; ring)
        (nd_of hp7 2 (by norm_num) (by norm_num) (by norm_num) ⟨(p:ℤ)^b, by ring⟩))
    · exact absurd hv (del_invalid hp _ (1 + (p:ℤ)^(v+1) + (p:ℤ)^(v+1+(b+1))) (1 + (p:ℤ)^(b+1)) 0
        hBd (by push_cast; ring)
        (nd_of hp7 1 (by norm_num) (by norm_num) (by norm_num)
          ⟨(p:ℤ)^v + (p:ℤ)^(v+(b+1)), by ring⟩))
    · exact absurd hv (del_invalid hp _ ((p:ℤ)^(u+1) + 1 + (p:ℤ)^(0+(b+1))) (1 + (p:ℤ)^(b+1)) 0
        hBd (by push_cast; ring)
        (nd_of hp7 1 (by norm_num) (by norm_num) (by norm_num)
          ⟨(p:ℤ)^u + (p:ℤ)^b, by ring⟩))
    · refine ⟨b+1, u, v, hb, by omega, ?_⟩
      rw [del_eq hp0 _ _ _ ((p:ℚ)^u + (p:ℚ)^v + (p:ℚ)^(v+(b+1))) hB (by push_cast; ring)]
  · -- E10 : 5 → 1, delete 2 then negate
    obtain ⟨b, u, v, hb, hc, rfl⟩ := hI
    have hB := hEne (p := p) b
    have hBd := hEdvd (p := p) b hb
    obtain ⟨hw, heq⟩ := post_step hp 5 1 2 true (fun _ => 2) _ hv
    rw [heq]; show D2Inv p n 1 _; simp only [D2Inv]
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rcases u with _ | u <;> rcases v with _ | v
    · refine ⟨b, by omega, ?_⟩
      congr 1
      refine (post_eval hp0 (-1) ((2:ℤ):ℚ) _ _ _ (-(p:ℚ)^b) hB (by push_cast; ring) ?_).trans ?_
      · rw [show (1 + (p:ℚ)^(b+1)) + p * ((2:ℤ):ℚ) * (-(p:ℚ)^b) = 1 - (p:ℚ)^(b+1) by
          push_cast; ring]
        exact one_sub_pow_ne hp (by omega)
      · simp only [pt]; push_cast; ring
    · exact absurd hw (del_invalid hp _ (1 + (p:ℤ)^(v+1) + (p:ℤ)^(v+1+(b+1))) (1 + (p:ℤ)^(b+1)) 2
        hBd (by push_cast; ring)
        (nd_of hp7 (-1) (by norm_num) (by norm_num) (by norm_num)
          ⟨(p:ℤ)^v + (p:ℤ)^(v+(b+1)), by ring⟩))
    · exact absurd hw (del_invalid hp _ ((p:ℤ)^(u+1) + 1 + (p:ℤ)^(0+(b+1))) (1 + (p:ℤ)^(b+1)) 2
        hBd (by push_cast; ring)
        (nd_of hp7 (-1) (by norm_num) (by norm_num) (by norm_num)
          ⟨(p:ℤ)^u + (p:ℤ)^b, by ring⟩))
    · exact absurd hw (del_invalid hp _ ((p:ℤ)^(u+1) + (p:ℤ)^(v+1) + (p:ℤ)^(v+1+(b+1)))
        (1 + (p:ℤ)^(b+1)) 2 hBd (by push_cast; ring)
        (nd_of hp7 (-2) (by norm_num) (by norm_num) (by norm_num)
          ⟨(p:ℤ)^u + (p:ℤ)^v + (p:ℤ)^(v+(b+1)), by ring⟩))

end IMMSol

namespace IMMSol
open IntegerMatrixMortality.FixedImage

lemma d2_res (p n : ℕ) (hp : p.Prime) : ∀ q x, D2Inv p n q x → InResidues p x delta := by
  intro q x hI
  match q, hI with
  | 0, hI => simp only [D2Inv] at hI; subst hI; exact inRes_pt hp _ (by omega)
  | 1, hI => obtain ⟨a, _, rfl⟩ := hI; exact inRes_pt hp _ (by omega)
  | 2, hI => obtain ⟨c, _, rfl⟩ := hI; exact inRes_pt hp _ (by omega)
  | 3, hI =>
    obtain ⟨c, j, hc, rfl⟩ := hI
    rcases j with _ | j
    · exact inres_frac hp _ 1 (1 - (p:ℤ)^(c+1) - (p:ℤ)^(n+1)) 1 (by simp [delta])
        (hDdvd _ _ (by omega) (by omega)) (by push_cast; ring) (by simp)
    · exact inres_frac hp _ ((p:ℤ)^(j+1)) (1 - (p:ℤ)^(c+1) - (p:ℤ)^(n+1)) 0 (by simp [delta])
        (hDdvd _ _ (by omega) (by omega)) (by push_cast; ring) ⟨(p:ℤ)^j, by ring⟩
  | 4, hI =>
    obtain ⟨c, b, i, hn, hb, rfl⟩ := hI
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rcases i with _ | i
    · exact inres_frac hp _ (1 + (p:ℤ)^(b+1)) (1 - (p:ℤ)^(c+1) - (p:ℤ)^(n+1)) 1
        (by simp [delta]) (hDdvd _ _ (by omega) (by omega)) (by push_cast; ring)
        ⟨(p:ℤ)^b, by ring⟩
    · exact inres_frac hp _ ((p:ℤ)^(i+1) + (p:ℤ)^(i+1+(b+1))) (1 - (p:ℤ)^(c+1) - (p:ℤ)^(n+1)) 0
        (by simp [delta]) (hDdvd _ _ (by omega) (by omega)) (by push_cast; ring)
        ⟨(p:ℤ)^i + (p:ℤ)^(i+(b+1)), by ring⟩
  | 5, hI =>
    obtain ⟨b, u, v, hb, hc, rfl⟩ := hI
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hBd := hEdvd (p := p) (b+1) (by omega)
    rcases u with _ | u <;> rcases v with _ | v
    · exact inres_frac hp _ (1 + 1 + (p:ℤ)^(0+(b+1))) (1 + (p:ℤ)^(b+1)) 2 (by simp [delta])
        hBd (by push_cast; ring) ⟨(p:ℤ)^b, by ring⟩
    · exact inres_frac hp _ (1 + (p:ℤ)^(v+1) + (p:ℤ)^(v+1+(b+1))) (1 + (p:ℤ)^(b+1)) 1
        (by simp [delta]) hBd (by push_cast; ring) ⟨(p:ℤ)^v + (p:ℤ)^(v+(b+1)), by ring⟩
    · exact inres_frac hp _ ((p:ℤ)^(u+1) + 1 + (p:ℤ)^(0+(b+1))) (1 + (p:ℤ)^(b+1)) 1
        (by simp [delta]) hBd (by push_cast; ring) ⟨(p:ℤ)^u + (p:ℤ)^b, by ring⟩
    · exact inres_frac hp _ ((p:ℤ)^(u+1) + (p:ℤ)^(v+1) + (p:ℤ)^(v+1+(b+1))) (1 + (p:ℤ)^(b+1)) 0
        (by simp [delta]) hBd (by push_cast; ring)
        ⟨(p:ℤ)^u + (p:ℤ)^v + (p:ℤ)^(v+(b+1)), by ring⟩
  | q+6, hI => exact False.elim hI

lemma pt_idx {p m m' N : ℕ} (h : m = m') : pt p m N = pt p m' N := by rw [h]

lemma T_eval {p : ℕ} (hp : p.Prime) (q r c N : ℕ) (hN : 1 ≤ N) :
    localAction p (GE q r 0 (fun _ => 0) false (fun _ => -1)) (some (pt p (c+1) N)) =
      some ((p:ℚ)^c / (1 - (p:ℚ)^(c+1) - (p:ℚ)^N)) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hB := one_sub_pow_ne hp hN
  have hD := hDne hp (c+1) N (by omega) hN
  refine (la_post_eval hp0 q r 0 false (fun _ => -1) ((p:ℚ)^(c+1)) (1 - (p:ℚ)^N) ((p:ℚ)^c) hB
    (by push_cast; ring) (by push_cast; convert hD using 1; ring)).trans ?_
  congr 1
  simp only [Bool.false_eq_true, if_false]
  push_cast; ring

lemma d2_guess {p : ℕ} (hp : p.Prime) (k n : ℕ) (hn : n = 2*k+1) :
    ∃ g : List GeneratorEdge, (∀ e ∈ g, e.target ≠ 1) ∧
      ValidWalk p div2Module.edges 0 (some (pt p n (n+1))) g 3
        (some ((p:ℚ)^k / (1 - (p:ℚ)^(k+1) - (p:ℚ)^(n+1)))) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hD := hDne hp (k+1) (n+1) (by omega) (by omega)
  have hval : Valid p (some ((p:ℚ)^k / (1 - (p:ℚ)^(k+1) - (p:ℚ)^(n+1)))) :=
    valid_frac hp _ ((p:ℤ)^k) (1 - (p:ℤ)^(k+1) - (p:ℤ)^(n+1)) (hDdvd _ _ (by omega) (by omega))
      (by push_cast; ring)
  rcases k with _ | k
  · refine ⟨[GE 0 3 0 (fun _ => 0) false (fun _ => -1)], by simp [GE], ?_⟩
    refine walk_cons _ (by rw [div2_edges]; simp) rfl (valid_pt hp _ (by omega)) ?_
      (ValidWalk.nil 3 _ hval)
    rw [pt_idx (show n = 0 + 1 by omega), T_eval hp _ _ _ _ (by omega)]
  · refine ⟨GE 0 2 0 :: (List.replicate k (GE 2 2 0) ++ [GE 2 3 0 (fun _ => 0) false (fun _ => -1)]),
      ?_, ?_⟩
    · intro e he
      simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
        or_false] at he
      rcases he with rfl | ⟨_, rfl⟩ | rfl <;> simp [GE]
    have hloop := loop_walk (p := p) (edges := div2Module.edges) (GE 2 2 0)
      (by rw [div2_edges]; simp) 2 rfl rfl (fun j => pt p (k+2+j) (n+1))
      (fun j => valid_pt hp _ (by omega))
      (fun j => by
        rw [la_plain p hp0, pt_idx (show k+2+(j+1) = (k+2+j)+1 by omega), del0_succ hp]) k
    refine walk_cons _ (by rw [div2_edges]; simp) rfl (valid_pt hp _ (by omega)) ?_
      (walk_append hloop ?_)
    · rw [la_plain p hp0, pt_idx (show n = (k+2+k)+1 by omega), del0_succ hp]
    · refine walk_cons _ (by rw [div2_edges]; simp) rfl (valid_pt hp _ (by omega)) ?_
        (ValidWalk.nil 3 _ hval)
      rw [pt_idx (show k+2+0 = (k+1)+1 by omega), T_eval hp _ _ _ _ (by omega)]

lemma frac_congr {a b c d : ℚ} (h1 : a = c) (h2 : b = d) : a / b = c / d := by rw [h1, h2]

end IMMSol

open IntegerMatrixMortality.FixedImage IMMSol in
theorem solution
    : ModuleRequirements div2Module (instructionUpdate .div2) ∧
      div2Module.edges.length = 10 := by
  refine ⟨⟨?_, ?_⟩, by rw [div2_edges]; rfl⟩
  · intro e he
    rw [div2_edges] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp [GE, delta], Computable.const _, Computable.const _⟩
  · intro p hp hp7
    have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine ⟨?_, ?_, ?_⟩
    · intro n w r y hw
      exact d2_res p n hp r y (walk_inv (D2Inv p n) (d2_step p n hp hp7) hw
        (by show D2Inv p n 0 _; rfl))
    · intro n k hk
      simp only [instructionUpdate] at hk
      split_ifs at hk with h
      simp only [Option.some.injEq] at hk
      have hn : n = 2*k+1 := by omega
      obtain ⟨g, hg, hwA⟩ := d2_guess hp k n hn
      subst hn
      set D : ℚ := 1 - (p:ℚ)^(k+1) - (p:ℚ)^(2*k+1+1) with hDdef
      have hD : D ≠ 0 := hDne hp (k+1) (2*k+1+1) (by omega) (by omega)
      have hDd : (p:ℤ) ∣ (1 - (p:ℤ)^(k+1) - (p:ℤ)^(2*k+1+1)) - 1 := hDdvd _ _ (by omega) (by omega)
      have hE : (1 + (p:ℚ)^(k+1)) ≠ 0 := hEne _
      have hEd : (p:ℤ) ∣ (1 + (p:ℤ)^(k+1)) - 1 := hEdvd _ (by omega)
      -- phase B: delete k zeros at state 3
      have hB := loop_walk (p := p) (edges := div2Module.edges) (GE 3 3 0)
        (by rw [div2_edges]; simp) 3 rfl rfl (fun j => (p:ℚ)^j / D)
        (fun j => valid_frac hp _ ((p:ℤ)^j) _ hDd (by rw [hDdef]; push_cast; ring))
        (fun j => la_plain_eval hp0 3 3 0 _ _ _ hD (by push_cast; ring)) k
      -- E6
      have h6 : localAction p (GE 3 4 1) (some ((p:ℚ)^0 / D)) =
          some (((p:ℚ)^k + (p:ℚ)^(k+(k+1))) / D) :=
        la_plain_eval hp0 3 4 1 _ _ _ hD (by rw [hDdef]; push_cast; ring)
      -- phase C
      have hC := loop_walk (p := p) (edges := div2Module.edges) (GE 4 4 0)
        (by rw [div2_edges]; simp) 4 rfl rfl (fun j => ((p:ℚ)^j + (p:ℚ)^(j+(k+1))) / D)
        (fun j => valid_frac hp _ ((p:ℤ)^j + (p:ℤ)^(j+(k+1))) _ hDd
          (by rw [hDdef]; push_cast; ring))
        (fun j => la_plain_eval hp0 4 4 0 _ _ _ hD (by push_cast; ring)) k
      -- E8
      have h8 : localAction p (GE 4 5 1 (fun _ => 0) false (fun _ => 1))
          (some (((p:ℚ)^0 + (p:ℚ)^(0+(k+1))) / D)) =
          some (((p:ℚ)^k + (p:ℚ)^k + (p:ℚ)^(k+(k+1))) / (1 + (p:ℚ)^(k+1))) := by
        refine (la_post_eval hp0 4 5 1 false (fun _ => 1) _ _
          ((p:ℚ)^k + (p:ℚ)^k + (p:ℚ)^(k+(k+1))) hD (by rw [hDdef]; push_cast; ring)
          (by convert hE using 1; rw [hDdef]; push_cast; ring)).trans ?_
        congr 1
        exact frac_congr (by simp) (by rw [hDdef]; push_cast; ring)
      -- phase D
      have hDD := loop_walk (p := p) (edges := div2Module.edges) (GE 5 5 0)
        (by rw [div2_edges]; simp) 5 rfl rfl
        (fun j => ((p:ℚ)^j + (p:ℚ)^j + (p:ℚ)^(j+(k+1))) / (1 + (p:ℚ)^(k+1)))
        (fun j => valid_frac hp _ ((p:ℤ)^j + (p:ℤ)^j + (p:ℤ)^(j+(k+1))) _ hEd
          (by push_cast; ring))
        (fun j => la_plain_eval hp0 5 5 0 _ _ _ hE (by push_cast; ring)) k
      -- E10
      have h10 : localAction p (GE 5 1 2 (fun _ => 0) true (fun _ => 2))
          (some (((p:ℚ)^0 + (p:ℚ)^0 + (p:ℚ)^(0+(k+1))) / (1 + (p:ℚ)^(k+1)))) =
          some (unaryCode p k) := by
        refine (la_post_eval hp0 5 1 2 true (fun _ => 2) _ _ (-(p:ℚ)^k) hE
          (by push_cast; ring)
          (by convert one_sub_pow_ne hp (N := k+1) (by omega) using 1; push_cast; ring)).trans ?_
        congr 1
        exact frac_congr (by simp) (by push_cast; ring)
      have hv6 : Valid p (some (((p:ℚ)^0 + (p:ℚ)^(0+(k+1))) / D)) :=
        valid_frac hp _ ((p:ℤ)^0 + (p:ℤ)^(0+(k+1))) _ hDd (by rw [hDdef]; push_cast; ring)
      have hv10 : Valid p (some (((p:ℚ)^0 + (p:ℚ)^0 + (p:ℚ)^(0+(k+1))) / (1 + (p:ℚ)^(k+1)))) :=
        valid_frac hp _ ((p:ℤ)^0 + (p:ℤ)^0 + (p:ℤ)^(0+(k+1))) _ hEd (by push_cast; ring)
      have hv0 : Valid p (some ((p:ℚ)^0 / D)) :=
        valid_frac hp _ ((p:ℤ)^0) _ hDd (by rw [hDdef]; push_cast; ring)
      have hwalk : ValidWalk p div2Module.edges 0 (some (pt p (2*k+1) (2*k+1+1)))
          (g ++ (List.replicate k (GE 3 3 0) ++ (GE 3 4 1 :: (List.replicate k (GE 4 4 0) ++
            (GE 4 5 1 (fun _ => 0) false (fun _ => 1) :: (List.replicate k (GE 5 5 0) ++
              [GE 5 1 2 (fun _ => 0) true (fun _ => 2)]))))))
          1 (some (unaryCode p k)) := by
        refine walk_append hwA (walk_append hB ?_)
        refine walk_cons _ (by rw [div2_edges]; simp) rfl hv0 h6 (walk_append hC ?_)
        refine walk_cons _ (by rw [div2_edges]; simp) rfl hv6 h8 (walk_append hDD ?_)
        refine walk_cons _ (by rw [div2_edges]; simp) rfl hv10 h10 (ValidWalk.nil 1 _ ?_)
        exact valid_pt hp k (N := k+1) (by omega)
      refine ⟨_, by simp, ?_, hwalk⟩
      rw [show g ++ (List.replicate k (GE 3 3 0) ++ (GE 3 4 1 :: (List.replicate k (GE 4 4 0) ++
            (GE 4 5 1 (fun _ => 0) false (fun _ => 1) :: (List.replicate k (GE 5 5 0) ++
              [GE 5 1 2 (fun _ => 0) true (fun _ => 2)]))))) =
          (g ++ List.replicate k (GE 3 3 0) ++ [GE 3 4 1] ++ List.replicate k (GE 4 4 0) ++
            [GE 4 5 1 (fun _ => 0) false (fun _ => 1)] ++ List.replicate k (GE 5 5 0)) ++
              [GE 5 1 2 (fun _ => 0) true (fun _ => 2)] by simp]
      apply firstArrival_append
      intro e he
      simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
        or_false] at he
      have key : ∀ e, e ∈ g ∨ e = GE 3 3 0 ∨ e = GE 3 4 1 ∨ e = GE 4 4 0 ∨
          e = GE 4 5 1 (fun _ => 0) false (fun _ => 1) ∨ e = GE 5 5 0 → e.target ≠ 1 := by
        rintro e (h | rfl | rfl | rfl | rfl | rfl)
        · exact hg e h
        all_goals simp [GE]
      apply key
      tauto
    · rintro n y ⟨w, _, _, hw⟩
      have hI := walk_inv (D2Inv p n) (d2_step p n hp hp7) hw (by show D2Inv p n 0 _; rfl)
      change D2Inv p n 1 y at hI
      obtain ⟨a, rfl, rfl⟩ := hI
      refine ⟨a, ?_, rfl⟩
      simp only [instructionUpdate]
      rw [if_pos (by omega)]
      congr 1; omega
