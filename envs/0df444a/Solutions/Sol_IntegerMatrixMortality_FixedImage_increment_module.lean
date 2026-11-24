-- Prove2me | solution 1 for IntegerMatrixMortality.FixedImage.increment_module
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:45:06.864895+00:00
-- url     : https://prove2.me/submissions/a8aadf77-cfac-4f2a-9d36-ec894cc38e49

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

def IncInv (p n : ℕ) (q : ℕ) (x : ProjectivePoint) : Prop :=
  (q = 0 ∧ x = some (pt p n (n+1))) ∨ (q = 2 ∧ ∃ m, x = some (pt p m (n+2))) ∨
  (q = 1 ∧ x = some (pt p (n+1) (n+2)))

lemma pre_inc {p : ℕ} (hp : p.Prime) (n : ℕ) :
    pt p n (n+1) / (p * (((fun p : ℕ => 1 - (p:ℤ)) p : ℤ) : ℚ) * pt p n (n+1) + 1) = pt p n (n+2) ∧
    (p * (((fun p : ℕ => 1 - (p:ℤ)) p : ℤ) : ℚ) * pt p n (n+1) + 1 ≠ 0) := by
  have h1 := one_sub_pow_ne hp (N := n+1) (by omega)
  have h2 := one_sub_pow_ne hp (N := n+2) (by omega)
  have e : (p * (((fun p : ℕ => 1 - (p:ℤ)) p : ℤ) : ℚ) * pt p n (n+1) + 1) =
      (1 - (p:ℚ)^(n+2)) / (1 - (p:ℚ)^(n+1)) := by
    simp only [pt]; push_cast; field_simp; ring
  rw [e]
  refine ⟨?_, div_ne_zero h2 h1⟩
  simp only [pt]; field_simp

lemma inc_step (p n : ℕ) (hp : p.Prime) : ∀ q x e, IncInv p n q x → e ∈ incrementModule.edges →
    e.source = q → Valid p x → Valid p (localAction p e x) →
    IncInv p n e.target (localAction p e x) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro q x e hI he hq hx hv
  simp only [incrementModule, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨hpre1, hpre2⟩ := pre_inc hp n
  rcases hI with ⟨rfl, rfl⟩ | ⟨rfl, m, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases he with rfl | rfl | rfl | rfl <;> simp only [GE] at hq <;> try omega
  · rw [la_pre p hp0 0 2 0 _ _ hpre2, hpre1] at hv ⊢
    rcases n with _ | m
    · exact absurd hv (del0_zero_invalid hp (by norm_num))
    · rw [del0_succ hp]; right; left; exact ⟨rfl, m, rfl⟩
  · rw [la_pre p hp0 0 1 1 _ _ hpre2, hpre1] at hv ⊢
    rcases n with _ | m
    · rw [del1_zero' hp (by norm_num)]; right; right; exact ⟨rfl, rfl⟩
    · exact absurd hv (del1_succ_invalid hp m (by omega))
  · rw [la_plain p hp0] at hv ⊢
    rcases m with _ | m
    · exact absurd hv (del0_zero_invalid hp (by omega))
    · rw [del0_succ hp]; right; left; exact ⟨rfl, m, rfl⟩
  · rw [la_plain p hp0] at hv ⊢
    rcases m with _ | m
    · rw [del1_zero' hp (by omega)]; right; right
      refine ⟨rfl, ?_⟩
      rw [show n + 2 - 1 = n + 1 by omega]
    · exact absurd hv (del1_succ_invalid hp m (by omega))

lemma inc_loop (p : ℕ) (hp : p.Prime) (N : ℕ) (hN : 1 ≤ N) : ∀ j : ℕ,
    ValidWalk p incrementModule.edges 2 (some (pt p j N)) (List.replicate j (GE 2 2 0) ++ [GE 2 1 1])
      1 (some (pt p (N-1) N)) := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro j
  induction j with
  | zero =>
    refine walk_cons (GE 2 1 1) (by simp [incrementModule]) rfl (valid_pt hp _ hN) ?_
      (ValidWalk.nil 1 _ (valid_pt hp _ hN))
    rw [la_plain p hp0, del1_zero' hp hN]
  | succ j ih =>
    refine walk_cons (GE 2 2 0) (by simp [incrementModule]) rfl (valid_pt hp _ hN) ?_ ih
    rw [la_plain p hp0, del0_succ hp]

end IMMSol

open IntegerMatrixMortality.FixedImage IMMSol in
theorem solution
    : ModuleRequirements incrementModule (instructionUpdate .inc) ∧
      incrementModule.edges.length = 4 := by
  refine ⟨⟨?_, ?_⟩, rfl⟩
  · intro e he
    simp only [incrementModule, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> refine ⟨by simp [GE, delta], ?_, ?_⟩ <;>
      first | exact computable_one_sub | exact Computable.const 0
  · intro p hp _
    have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine ⟨?_, ?_, ?_⟩
    · intro n w r y hw
      have := walk_inv (IncInv p n) (inc_step p n hp) hw (Or.inl ⟨rfl, rfl⟩)
      rcases this with ⟨_, rfl⟩ | ⟨_, m, rfl⟩ | ⟨_, rfl⟩ <;> exact inRes_pt hp _ (by omega)
    · intro n k hk
      simp only [instructionUpdate, Option.some.injEq] at hk
      subst hk
      obtain ⟨hpre1, hpre2⟩ := pre_inc hp n
      rcases n with _ | m
      · rw [show unaryCode p 0 = pt p 0 (0+1) from rfl]
        refine ⟨[GE 0 1 1 (fun p => 1 - (p:ℤ))], by simp, ?_, ?_⟩
        · intro i hi; simp at hi
        · refine walk_cons _ (by simp [incrementModule]) rfl (valid_pt hp _ (by omega)) ?_
            (ValidWalk.nil 1 _ (valid_pt hp 1 (N := 2) (by omega)))
          rw [la_pre p hp0 0 1 1 _ _ hpre2, hpre1, del1_zero' hp (by norm_num)]
          rfl
      · rw [show unaryCode p (m+1) = pt p (m+1) (m+1+1) from rfl]
        refine ⟨GE 0 2 0 (fun p => 1 - (p:ℤ)) :: (List.replicate m (GE 2 2 0) ++ [GE 2 1 1]),
          by simp, ?_, ?_⟩
        · rw [← List.cons_append]
          apply firstArrival_append
          intro e he
          simp only [List.mem_cons, List.mem_replicate] at he
          rcases he with rfl | ⟨_, rfl⟩ <;> simp [GE, incrementModule]
        · have hl := inc_loop p hp (m+1+2) (by omega) m
          rw [show m + 1 + 2 - 1 = m + 1 + 1 by omega] at hl
          refine walk_cons _ (by simp [incrementModule]) rfl (valid_pt hp _ (by omega)) ?_ hl
          rw [la_pre p hp0 0 2 0 _ _ hpre2, hpre1, del0_succ hp]
    · rintro n y ⟨w, _, _, hw⟩
      have := walk_inv (IncInv p n) (inc_step p n hp) hw (Or.inl ⟨rfl, rfl⟩)
      refine ⟨n+1, rfl, ?_⟩
      rcases this with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
      · simp [incrementModule] at h
      · simp [incrementModule] at h
      · rfl
