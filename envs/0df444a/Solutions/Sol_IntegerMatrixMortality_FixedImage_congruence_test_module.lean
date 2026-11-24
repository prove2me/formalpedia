-- Prove2me | solution 1 for IntegerMatrixMortality.FixedImage.congruence_test_module
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:24:18.625295+00:00
-- url     : https://prove2.me/submissions/7f191db9-ff8d-4b58-82fd-eb2b9a569f8b

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

lemma test_mem (d : ℕ) (A : Finset ℕ) (e : GeneratorEdge) : e ∈ (testModule d A).edges ↔
    (e = GE 0 (2 + 1 % d) 0 ∨ (∃ j, j < d ∧ GE (2+j) (2+(j+1)%d) 0 = e)) ∨
      (∃ j, j ∈ A ∧ GE (2+j) 1 1 = e) ∨ (0 ∈ A ∧ e = GE 0 1 1) := by
  simp only [testModule, List.mem_append, List.mem_singleton, List.mem_map, List.mem_range,
    Finset.mem_sort]
  split_ifs with h <;> simp [h, or_assoc]

def TInv (p n d : ℕ) (A : Finset ℕ) (q : ℕ) (x : ProjectivePoint) : Prop :=
  (q = 0 ∧ x = some (pt p n (n+1))) ∨
  (∃ m k, 1 ≤ k ∧ m + k = n ∧ q = 2 + k % d ∧ x = some (pt p m (n+1))) ∨
  (q = 1 ∧ x = some (pt p n (n+1)) ∧ n % d ∈ A)

lemma mod_succ_eq (k d : ℕ) : (k % d + 1) % d = (k + 1) % d := by
  rw [Nat.add_mod (k % d), Nat.mod_mod, ← Nat.add_mod]

lemma test_step (p n d : ℕ) (A : Finset ℕ) (hp : p.Prime) : ∀ q x e, TInv p n d A q x →
    e ∈ (testModule d A).edges → e.source = q → Valid p x → Valid p (localAction p e x) →
    TInv p n d A e.target (localAction p e x) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro q x e hI he hq hx hv
  rw [test_mem] at he
  rcases he with (rfl | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩ | ⟨h0, rfl⟩ <;> simp only [GE] at hq <;>
    subst hq <;>
    rcases hI with ⟨hq, rfl⟩ | ⟨m, k, hk, hmk, hq, rfl⟩ | ⟨hq, rfl, hA⟩ <;>
    (try omega) <;> rw [la_plain p hp0] at hv ⊢
  · -- entry, delete 0
    rcases n with _ | m
    · exact absurd hv (del0_zero_invalid hp (by norm_num))
    · rw [del0_succ hp]
      right; left
      exact ⟨m, 1, le_refl _, by omega, rfl, rfl⟩
  · -- cycle edge
    have hjk : j = k % d := by omega
    subst hjk
    rcases m with _ | m
    · exact absurd hv (del0_zero_invalid hp (by omega))
    · rw [del0_succ hp]
      right; left
      refine ⟨m, k+1, by omega, by omega, ?_, rfl⟩
      show 2 + (k % d + 1) % d = 2 + (k+1) % d
      rw [mod_succ_eq]
  · -- marker edge
    have hjk : j = k % d := by omega
    subst hjk
    rcases m with _ | m
    · rw [del1_zero' hp (by omega)]
      right; right
      refine ⟨rfl, by rw [show n + 1 - 1 = n by omega], ?_⟩
      rwa [show n = k by omega]
    · exact absurd hv (del1_succ_invalid hp m (by omega))
  · -- direct exit
    rcases n with _ | m
    · rw [del1_zero' hp (by norm_num)]
      right; right
      exact ⟨rfl, rfl, by simpa using h0⟩
    · exact absurd hv (del1_succ_invalid hp m (by omega))

lemma test_loop (p n d : ℕ) (A : Finset ℕ) (hp : p.Prime) (hd : 1 ≤ d) (hA : n % d ∈ A) :
    ∀ t k, k + t = n →
      ValidWalk p (testModule d A).edges (2 + k % d) (some (pt p t (n+1)))
        ((List.range' k t).map (fun i => GE (2 + i % d) (2 + (i % d + 1) % d) 0) ++
          [GE (2 + n % d) 1 1]) 1 (some (pt p n (n+1))) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro t
  induction t with
  | zero =>
    intro k hk
    have : k = n := by omega
    subst this
    refine walk_cons _ ?_ rfl (valid_pt hp _ (by omega)) ?_
      (ValidWalk.nil 1 _ (valid_pt hp _ (by omega)))
    · rw [test_mem]; right; left; exact ⟨_, hA, rfl⟩
    · rw [la_plain p hp0, del1_zero' hp (by omega), show k + 1 - 1 = k by omega]
  | succ t ih =>
    intro k hk
    simp only [List.range'_succ, List.map_cons, List.cons_append]
    refine walk_cons (x' := some (pt p t (n+1))) _ ?_ rfl (valid_pt hp _ (by omega)) ?_ ?_
    · rw [test_mem]; left; right
      exact ⟨k % d, Nat.mod_lt _ (by omega), rfl⟩
    · rw [la_plain p hp0, del0_succ hp]
    · have := ih (k+1) (by omega)
      show ValidWalk p _ (2 + (k % d + 1) % d) _ _ _ _
      rw [mod_succ_eq]
      exact this

end IMMSol

open IntegerMatrixMortality.FixedImage IMMSol in
theorem solution
    (d : ℕ) (A : Finset ℕ) (hd : 1 ≤ d) (hA : ∀ a ∈ A, a < d) :
      ModuleRequirements (testModule d A) (instructionUpdate (.test d A)) ∧
      (testModule d A).edges.length = 1+d+A.card+(if 0 ∈ A then 1 else 0) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    rw [test_mem] at he
    rcases he with (rfl | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩ | ⟨h0, rfl⟩ <;>
      exact ⟨by simp [GE, delta], Computable.const _, Computable.const _⟩
  · intro p hp _
    have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine ⟨?_, ?_, ?_⟩
    · intro n w r y hw
      have := walk_inv (TInv p n d A) (test_step p n d A hp) hw (Or.inl ⟨rfl, rfl⟩)
      rcases this with ⟨_, rfl⟩ | ⟨m, k, _, _, _, rfl⟩ | ⟨_, rfl, _⟩ <;>
        exact inRes_pt hp _ (by omega)
    · intro n k hk
      simp only [instructionUpdate] at hk
      split_ifs at hk with hn
      simp only [Option.some.injEq] at hk
      subst hk
      rcases n with _ | m
      · refine ⟨[GE 0 1 1], by simp, ?_, ?_⟩
        · intro i hi; simp at hi
        · refine walk_cons _ ?_ rfl (valid_pt hp _ (by omega)) ?_
            (ValidWalk.nil 1 _ (valid_pt hp 0 (N := 0+1) (by omega)))
          · rw [test_mem]; right; right
            exact ⟨by simpa using hn, rfl⟩
          · show localAction p (GE 0 1 1) (some (pt p 0 (0+1))) = _
            rw [la_plain p hp0, del1_zero' hp (by omega)]
            rfl
      · refine ⟨GE 0 (2 + 1 % d) 0 :: ((List.range' 1 m).map
            (fun i => GE (2 + i % d) (2 + (i % d + 1) % d) 0) ++ [GE (2 + (m+1) % d) 1 1]),
          by simp, ?_, ?_⟩
        · rw [← List.cons_append]
          apply firstArrival_append
          intro e he
          simp only [List.mem_cons, List.mem_map, List.mem_range'] at he
          rcases he with rfl | ⟨i, _, rfl⟩ <;> simp [GE, testModule] <;> omega
        · refine walk_cons _ ?_ rfl (valid_pt hp _ (by omega)) ?_
            (test_loop p (m+1) d A hp hd hn m 1 (by omega))
          · rw [test_mem]; left; left; rfl
          · show localAction p (GE 0 (2 + 1 % d) 0) (some (pt p (m+1) (m+1+1))) = _
            rw [la_plain p hp0, del0_succ hp]
    · rintro n y ⟨w, _, _, hw⟩
      have := walk_inv (TInv p n d A) (test_step p n d A hp) hw (Or.inl ⟨rfl, rfl⟩)
      rcases this with ⟨h, _⟩ | ⟨m, k, _, _, h, _⟩ | ⟨_, rfl, hA'⟩
      · simp [testModule] at h
      · simp [testModule] at h <;> omega
      · refine ⟨n, ?_, rfl⟩
        simp [instructionUpdate, hA']
  · simp only [testModule, List.length_append, List.length_map, List.length_range,
      Finset.length_sort, List.length_singleton]
    split_ifs <;> simp
