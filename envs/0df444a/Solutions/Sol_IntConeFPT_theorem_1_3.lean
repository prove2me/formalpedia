-- Prove2me | solution 3 for IntConeFPT.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T08:44:50.157079+00:00
-- url     : https://prove2.me/submissions/17f40328-f82a-4fa5-85db-8d034726e823
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Definitions.Def_IntConeFPT_Homogenized
import Theorems.Thm_IntConeFPT_polytope_height_product
import Theorems.Thm_IntConeFPT_proposition_14
import Theorems.Thm_IntConeFPT_short_recession_step
import Theorems.Thm_IntConeFPT_sparse_perspective_projection
import Theorems.Thm_IntConeFPT_lemma_7
import Theorems.Thm_IntConeFPT_section_B3_unboundedness
import Theorems.Thm_IntConeFPT_section_3_6_nstar_bound
import Theorems.Thm_IntConeFPT_section_3_6_driver

set_option autoImplicit false

open OnlineCRS.Combine

open IntConeFPT OnlineCRS.Combine RobustToDynamics Turing
namespace IntConeFPT.LinearBox

private abbrev tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Sym
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m
    | false => .push true (fun _ => 1) (.goto (fun _ => true))
    | true => .pop false (fun _ x => x.isSome)
        (.branch id (.push true (fun _ => 0) (.goto (fun _ => true))) .halt)

private def W : Machine := ⟨tm, Equiv.refl _, Equiv.refl _⟩

private def cfg (l : Option Bool) (v : Bool) (i o : List Sym) : tm.Cfg :=
  ⟨l, v, fun (k : Bool) => if k then o else i⟩

private lemma initStep (i : List Sym) :
    tm.step (initList tm i) = some (cfg (some true) false i [1]) := by
  apply congrArg some
  apply TM2.Cfg.mk.injEq .. |>.mpr
  refine ⟨rfl, rfl, funext fun k => ?_⟩
  cases k <;> rfl

private lemma consStep (v : Bool) (x : Sym) (i o : List Sym) :
    tm.step (cfg (some true) v (x::i) o) = some (cfg (some true) true i (0::o)) := by
  apply congrArg some
  apply TM2.Cfg.mk.injEq .. |>.mpr
  refine ⟨rfl, rfl, funext fun k => ?_⟩
  cases k <;> rfl

private lemma nilStep (v : Bool) (o : List Sym) :
    tm.step (cfg (some true) v [] o) = some (haltList tm o) := by
  apply congrArg some
  apply TM2.Cfg.mk.injEq .. |>.mpr
  refine ⟨rfl, rfl, funext fun k => ?_⟩
  cases k <;> rfl

private lemma loop (i o : List Sym) (v : Bool) :
    (flip Option.bind tm.step)^[i.length + 1] (some (cfg (some true) v i o)) =
      some (haltList tm (List.replicate i.length 0 ++ o)) := by
  induction i generalizing o v with
  | nil => exact nilStep v o
  | cons x i ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Option.bind tm.step)^[i.length + 1] (tm.step (cfg (some true) v (x::i) o)) = _
    rw [consStep, ih, List.replicate_succ', List.append_assoc]
    rfl

private lemma run (w : List Sym) : RunsWithin W w (List.replicate w.length 0 ++ [1])
    ((w.length + 2 : ℕ) : ℝ) := by
  refine ⟨w.length + 2, le_rfl, ⟨⟨⟨w.length + 2, ?_⟩, le_rfl⟩⟩⟩
  change (flip Option.bind tm.step)^[w.length + 2] (some (initList tm (w.map id))) =
    some (haltList tm ((List.replicate w.length (0 : Sym) ++ [1]).map id))
  simp only [List.map_id]
  rw [Function.iterate_succ_apply]
  change (flip Option.bind tm.step)^[w.length + 1] (tm.step (initList tm w)) = _
  rw [initStep, loop]

private def digits : ℕ → PosNum
  | 0 => .one
  | n+1 => .bit0 (digits n)

private lemma encPow (n : ℕ) : encNat (2 ^ n) = List.replicate n 0 ++ [1] := by
  have val : ∀ k, (digits k : ℕ) = 2 ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [digits, PosNum.cast_bit0, ih, pow_succ, Nat.mul_two]
  unfold encNat Computability.encodeNat
  rw [← val n, PosNum.of_to_nat]
  change (Computability.encodePosNum (digits n)).map bit = _
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [digits, Computability.encodePosNum, List.replicate_succ, bit] using
      congrArg (List.cons (0 : Sym)) ih

private lemma bitCap (n : ℕ) : n < 2 ^ (encNat n).length := by
  have hp (p : PosNum) : (p : ℕ) < 2 ^ (Computability.encodePosNum p).length := by
    induction p with
    | one => decide
    | bit0 p ih => simp [Computability.encodePosNum, PosNum.cast_bit0, pow_succ]; omega
    | bit1 p ih => simp [Computability.encodePosNum, PosNum.cast_bit1, pow_succ]; omega
  simp only [encNat, List.length_map, Computability.encodeNat]
  conv_lhs => rw [← Num.to_of_nat n]
  cases (n : Num) with
  | zero => decide
  | pos p => exact hp p

private def H (q : ℚ) := (q.num.natAbs + 1) * q.den

private lemma height (q : ℚ) : H q ≤ 2 ^ (encRat q).length := by
  have h := Nat.mul_le_mul (bitCap q.num.natAbs) (bitCap q.den).le
  unfold H
  refine h.trans ?_
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  simp [encRat, encInt]; omega

private lemma concatCap {α : Type} (h : α → ℕ) (f : α → List Sym)
    (hf : ∀ x, h x ≤ 2 ^ (f x).length) (xs : List α) :
    (xs.map h).prod ≤ 2 ^ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa [pow_add] using Nat.mul_le_mul (hf x) ih

private lemma vecCap {k : ℕ} (x : Fin k → ℚ) : ∏ j, H (x j) ≤ 2 ^ (encVec x).length := by
  rw [Fin.prod_univ_def]
  apply concatCap
  intro j
  exact (height _).trans (Nat.pow_le_pow_right (by decide) (by simp))

private lemma matCap {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℚ) :
    ∏ i, ∏ j, H (A i j) ≤ 2 ^ (encMat A).length := by
  rw [Fin.prod_univ_def]
  apply concatCap
  intro i
  exact (vecCap (A i)).trans (Nat.pow_le_pow_right (by decide) (by simp))

private lemma block_le {α β : Type} (f : α → List β) {x : α} {xs : List α}
    (hx : x ∈ xs) : (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h
      omega

end IntConeFPT.LinearBox
open IntConeFPT.LinearBox

private theorem linear_box_bound :
    ∃ C : ℕ, ∃ Mtm : Machine, ∀ I : Instance, I.Valid →
      ∃ M : ℕ, 1 ≤ M ∧ (∀ t, ∀ p ∈ I.P t, InBox M p) ∧
        (encNat M).length ≤ (encInstance I).length ^ C ∧
        RunsWithin Mtm (encInstance I) (encNat M) (((encInstance I).length : ℝ) ^ C) := by
  refine ⟨2, W, ?_⟩
  intro I hI
  let L := (encInstance I).length
  have hL : 2 ≤ L := by simp [L, encInstance]; omega
  have hsq : L+2 ≤ L^2 := by nlinarith
  refine ⟨2^L, Nat.one_le_two_pow, ?_, ?_, ?_⟩
  · intro t p hp
    have h := polytope_height_product (I.Aloc t) (I.Bloc t) (I.bloc t) (hI.bounded t) p hp
    let f := fun t => encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++
      encVec (I.bloc t) ++ [3] ++ encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3]
    have hh := block_le f (List.mem_finRange t)
    have hs : (encMat (I.Aloc t)).length + (encMat (I.Bloc t)).length +
        (encVec (I.bloc t)).length ≤ L := by
      dsimp [f] at hh
      simp only [L, encInstance, List.length_append, List.length_cons, List.length_nil] at hh ⊢
      omega
    have hh' := Nat.mul_le_mul (Nat.mul_le_mul (matCap (I.Aloc t)) (matCap (I.Bloc t))) (vecCap (I.bloc t))
    rw [← pow_add, ← pow_add] at hh'
    have hfinal := hh'.trans (Nat.pow_le_pow_right (by decide) hs)
    exact ⟨fun j => (h.1 j).trans (Nat.cast_le.mpr hfinal), fun j => (h.2 j).trans (Nat.cast_le.mpr hfinal)⟩
  · rw [encPow]
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    exact (Nat.le_succ _).trans hsq
  · rw [encPow]
    obtain ⟨m, hm, hr⟩ := run (encInstance I)
    exact ⟨m, hm.trans (by exact_mod_cast hsq), hr⟩


open IntConeFPT
namespace IntConeFPT.CountPeeling

private lemma convex_P (I : Instance) (t : Fin I.τ) : Convex ℝ (I.P t) := by
  intro p hp q hq a b ha hb hab i
  have hpi := hp i
  have hqi := hq i
  have hsum :
      (∑ j, (I.Aloc t i j : ℝ) * (a • p + b • q).1 j) +
      (∑ j, (I.Bloc t i j : ℝ) * (a • p + b • q).2 j) =
      a * ((∑ j, (I.Aloc t i j : ℝ) * p.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p.2 j)) +
      b * ((∑ j, (I.Aloc t i j : ℝ) * q.1 j) + (∑ j, (I.Bloc t i j : ℝ) * q.2 j)) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_left_comm, ← Finset.mul_sum]
    ring
  rw [hsum]
  calc
    _ ≤ a * (I.bloc t i : ℝ) + b * (I.bloc t i : ℝ) := add_le_add (mul_le_mul_of_nonneg_left hpi ha) (mul_le_mul_of_nonneg_left hqi hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

private lemma discreteJensen_X (I : Instance) (hI : I.Valid) (t : Fin I.τ) :
    DiscreteJensen {x : Fin I.d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' I.P t}
      (fun x => I.f t (fun i => (x i : ℝ))) := by
  intro x _ m θ xs hxs hθ0 hθ1 hx_eq
  have hconv := hI.convex t
  have hle := hconv.map_sum_le (fun i _ => hθ0 i) hθ1 (fun i _ => hxs i)
  rw [← hx_eq] at hle
  simpa only [smul_eq_mul] using hle

private lemma exists_global_opt_of_bdd_below (I : Instance)
    (hfeas : ∃ μ, I.Feasible μ)
    (hbdd : ∃ L : ℝ, ∀ μ, I.Feasible μ → L ≤ I.cost μ) :
    ∃ μ_opt : Mult I, I.Feasible μ_opt ∧ ∀ μ : Mult I, I.Feasible μ → I.cost μ_opt ≤ I.cost μ := by
  obtain ⟨L, hL⟩ := hbdd
  let Q_den : ℕ := ∏ t : Fin I.τ, ∏ j : Fin (monomials I.d (I.deg t)).length, (I.coeff t j).den
  have hQ_pos : 0 < Q_den := by
    refine Finset.prod_pos fun t _ => Finset.prod_pos fun j _ => (I.coeff t j).pos
  let coeffZ : (t : Fin I.τ) → Fin (monomials I.d (I.deg t)).length → ℤ := fun t j =>
    (I.coeff t j).num * ((Q_den / (I.coeff t j).den : ℕ) : ℤ)
  have hcoeff_eq : ∀ t j, (coeffZ t j : ℝ) = (Q_den : ℝ) * (I.coeff t j : ℝ) := by
    intro t j
    have hdvd : (I.coeff t j).den ∣ Q_den :=
      dvd_trans (Finset.dvd_prod_of_mem (fun j => (I.coeff t j).den) (Finset.mem_univ j))
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ t))
    have hmul_den : ((Q_den / (I.coeff t j).den : ℕ) : ℝ) * ((I.coeff t j).den : ℝ) = (Q_den : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hden_ne : ((I.coeff t j).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (I.coeff t j).pos.ne'
    have hq_eq : (I.coeff t j : ℝ) = ((I.coeff t j).num : ℝ) / ((I.coeff t j).den : ℝ) := by
      rw [Rat.cast_def]
    calc (coeffZ t j : ℝ)
      _ = ((I.coeff t j).num : ℝ) * ((Q_den / (I.coeff t j).den : ℕ) : ℝ) := by
          simp only [coeffZ, Int.cast_mul, Int.cast_natCast]
      _ = ((I.coeff t j).num : ℝ) * ((Q_den : ℝ) / ((I.coeff t j).den : ℝ)) := by
          rw [(eq_div_iff hden_ne).mpr hmul_den]
      _ = (Q_den : ℝ) * (((I.coeff t j).num : ℝ) / ((I.coeff t j).den : ℝ)) := by ring
      _ = (Q_den : ℝ) * (I.coeff t j : ℝ) := by rw [← hq_eq]
  have hcost_int : ∀ μ : Mult I, ∃ z : ℤ, (Q_den : ℝ) * I.cost μ = (z : ℝ) := by
    intro μ
    let fZ : (t : Fin I.τ) → (Fin I.d → ℤ) → ℤ := fun t x =>
      ∑ j : Fin (monomials I.d (I.deg t)).length,
        coeffZ t j * ∏ i, x i ^ ((monomials I.d (I.deg t)).get j i)
    refine ⟨∑ t : Fin I.τ, (μ t).sum fun g n => (n : ℤ) * fZ t g.1, ?_⟩
    unfold Instance.cost costOf
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hf_eq : (Q_den : ℝ) * ((μ t g : ℝ) * I.f t (fun i => (g.1 i : ℝ))) =
        (μ t g : ℝ) * (fZ t g.1 : ℝ) := by
      rw [mul_left_comm]
      congr 1
      simp only [fZ, Instance.f, Finset.mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_prod,
        Int.cast_pow, hcoeff_eq]
      refine Finset.sum_congr rfl fun j _ => by ring
    exact hf_eq
  let P_int : ℤ → Prop := fun z => ∃ μ, I.Feasible μ ∧ (Q_den : ℝ) * I.cost μ = (z : ℝ)
  have hP_bdd : ∃ b : ℤ, ∀ z : ℤ, P_int z → b ≤ z := by
    refine ⟨Int.floor ((Q_den : ℝ) * L), fun z ⟨μ, hμ, hμ_eq⟩ => ?_⟩
    have h1 : (Q_den : ℝ) * L ≤ (Q_den : ℝ) * I.cost μ :=
      mul_le_mul_of_nonneg_left (hL μ hμ) (Nat.cast_nonneg _)
    rw [hμ_eq] at h1
    exact_mod_cast (Int.floor_le _).trans h1
  have hP_inh : ∃ z : ℤ, P_int z := by
    obtain ⟨μ₀, hμ₀⟩ := hfeas
    obtain ⟨z₀, hz₀⟩ := hcost_int μ₀
    exact ⟨z₀, μ₀, hμ₀, hz₀⟩
  obtain ⟨z_min, ⟨μ_opt, hμ_opt, hμ_opt_eq⟩, hz_min⟩ := Int.exists_least_of_bdd hP_bdd hP_inh
  refine ⟨μ_opt, hμ_opt, fun μ hμ => ?_⟩
  obtain ⟨z, hz⟩ := hcost_int μ
  have hz_le : (z_min : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_min z ⟨μ, hμ, hz⟩
  rw [← hμ_opt_eq, ← hz] at hz_le
  exact le_of_mul_le_mul_left hz_le (Nat.cast_pos.mpr hQ_pos)

private lemma nstar_mono_bound (I : Instance) (U : ℕ) (hU : 1 ≤ U)
    {p : ℕ} (hp_le : p ≤ I.τ * 2 ^ I.d) :
    p * (p + 1) * p.factorial * ((I.τ * 2 ^ I.d * I.k + 1).factorial * U ^ (I.τ * 2 ^ I.d * I.k + 1)) ^ p ≤
      Nstar I.τ I.d I.k U := by
  let s := I.τ * 2 ^ I.d
  let H := (s * I.k + 1).factorial * U ^ (s * I.k + 1)
  have hH1 : 1 ≤ H := Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos hU)
  change p * (p + 1) * p.factorial * H ^ p ≤ s * (s + 1) * s.factorial * H ^ s
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul hp_le (Nat.add_le_add_right hp_le 1)) (Nat.factorial_le hp_le))
    (Nat.pow_le_pow_right hH1 hp_le)

private abbrev lhs {p m : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (z : Fin p → ℕ) (i : Fin m) :=
  ∑ j, A i j * (z j : ℤ)

private abbrev price {p : ℕ} (c : Fin p → ℝ) (z : Fin p → ℕ) := ∑ j, (z j : ℝ) * c j

private lemma price_add {p : ℕ} (c : Fin p → ℝ) (y r : Fin p → ℕ) :
    price c (y+r) = price c y + price c r := by simp [price, add_mul, Finset.sum_add_distrib]

private lemma lhs_add {p m : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (y r : Fin p → ℕ) (i : Fin m) :
    lhs A (y+r) i = lhs A y i + lhs A r i := by simp [lhs, mul_add, Finset.sum_add_distrib]

private lemma peel {p m H : ℕ} (hp : 1 ≤ p) (hH : 1 ≤ H)
    (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ H) (hb : ∀ i, |b i| ≤ H)
    (c : Fin p → ℝ) (z : Fin p → ℕ) (hz : ∀ i, lhs A z i ≤ b i) :
    let B := p * (p+1) * p.factorial * H ^ p
    (∃ y, (∀ i, lhs A y i ≤ b i) ∧ (∑ j, y j) ≤ B ∧ price c y ≤ price c z) ∨
    (∃ r, (∀ i, lhs A r i ≤ 0) ∧ (∑ j, r j) ≤ B ∧ price c r < 0) := by
  intro B
  by_cases h : (∑ j, z j) ≤ B
  · exact Or.inl ⟨z, hz, h, le_rfl⟩
  obtain ⟨y,r,he,hy,hr,hrpos,hrle⟩ := short_recession_step hp hH A b hA hb z hz (lt_of_not_ge h)
  by_cases hn : price c r < 0
  · exact Or.inr ⟨r,hr,hrle,hn⟩
  have hylt : (∑ j, y j) < ∑ j, z j := by simpa [he, Finset.sum_add_distrib]
  rcases peel hp hH A b hA hb c y hy with ⟨y',hy',hsize,hcost⟩ | ray
  · exact Or.inl ⟨y',hy',hsize,hcost.trans (by rw [he, price_add]; linarith)⟩
  · exact Or.inr ray
termination_by ∑ j, z j

private lemma sparse (I : Instance) (hI : I.Valid) (μ : Mult I) (hs : I.Supported μ) :
    ∃ ν : Mult I, I.Supported ν ∧ (∀ t, I.typeAgg ν t = I.typeAgg μ t) ∧
      I.cost ν ≤ I.cost μ ∧ (∑ t, (ν t).support.card) ≤ I.τ * 2 ^ I.d := by
  obtain ⟨ν, hv, ha, hc, _, hsiz⟩ :=
    lemma_7 hI.one_le_d I.P (convex_P I) hI.bounded I.f (discreteJensen_X I hI) μ hs
  exact ⟨ν,hv,fun t => by simp [Instance.typeAgg, (ha t).1, (ha t).2],
    Finset.sum_le_sum (fun t _ => hc t),hsiz⟩

-- For a bounded optimum the 'negative ray' branch contradicts optimality after lifting z+r.
-- For a homogeneous problem the ray itself is a feasible witness.
private lemma compress (I : Instance) (hI : I.Valid) (M U : ℕ)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (hU : 1 ≤ U) (D : IntDesc I)
    (hD : D.Describes) (hDU : D.BoundedBy M U)
    (rhs : Fin D.mW → ℤ) (hrhs : ∀ i, |rhs i| ≤ U)
    (μ : Mult I) (hs : I.Supported μ)
    (ha : ∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ rhs i)
    (mode : Fin 3)
    (hopt : mode = 1 → ∀ ν : Mult I, I.Supported ν →
      (∀ i, D.aggLHS (fun t => I.typeAgg ν t) i ≤ rhs i) → I.cost μ ≤ I.cost ν)
    (hhom : mode = 2 → rhs = 0 ∧ I.cost μ < 0) :
    ∃ ν : Mult I, I.Supported ν ∧ (∀ i, D.aggLHS (fun t => I.typeAgg ν t) i ≤ rhs i) ∧
      I.totalCount ν ≤ Nstar I.τ I.d I.k U ∧
      (mode = 1 → I.cost ν ≤ I.cost μ) ∧ (mode = 2 → I.cost ν < 0) := by
  obtain ⟨v,vs,va,vc,vsiz⟩ := sparse I hI μ hs
  have vagg : ∀ i, D.aggLHS (fun t => I.typeAgg v t) i ≤ rhs i := by simpa only [va] using ha
  by_cases hcnt : I.totalCount v = 0
  · exact ⟨v,vs,vagg,hcnt ▸ Nat.zero_le _,fun _ => vc,fun e => vc.trans_lt (hhom e).2⟩
  obtain ⟨p,m,A,b,c,z,hp,hps,hA,hb,hb0,hz,hzc,lift⟩ :=
    sparse_perspective_projection I hI M U hbox hU D hD hDU v vs vsiz (Nat.pos_of_ne_zero hcnt)
      rhs hrhs vagg
  let H := (I.τ * 2^I.d * I.k + 1).factorial * U ^ (I.τ * 2^I.d * I.k + 1)
  have hH : 1 ≤ H := Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos hU)
  have hn := nstar_mono_bound I U hU hps
  let w : Fin p → ℝ := if mode = 0 then 0 else c
  rcases peel hp hH A b hA hb w z hz with ⟨y,hy,hyN,hyc⟩ | ⟨r,hr,hrN,hrc⟩
  · obtain ⟨ν,hν,hνa,hνn,hνc⟩ := lift y hy
    refine ⟨ν,hν,hνa,hνn ▸ hyN.trans hn,?_,?_⟩
    · intro e
      have he : w = c := by simp [w,e]
      rw [he] at hyc
      exact hνc.le.trans (hyc.trans (hzc.le.trans vc))
    · intro e
      have he : w = c := by simp [w,e]
      rw [he] at hyc
      exact (hνc.le.trans (hyc.trans (hzc.le.trans vc))).trans_lt (hhom e).2
  · by_cases h0 : mode = 0
    · simp [w,h0,price] at hrc
    have he : w = c := if_neg h0
    rw [he] at hrc
    by_cases h1 : mode = 1
    · obtain ⟨ν,hν,hνa,_,hcost⟩ := lift (z+r) (fun i => by
        change lhs A (z+r) i ≤ _
        rw [lhs_add]; linarith [hz i, hr i])
      have hbad := hopt h1 ν hν hνa
      change I.cost ν = price c (z+r) at hcost
      change price c z = I.cost v at hzc
      rw [price_add, hzc] at hcost
      linarith
    have h2 : mode = 2 := by fin_cases mode <;> simp_all
    obtain ⟨ν,hν,hνa,hνn,hνc⟩ := lift r (fun i => by simpa [hb0 (hhom h2).1] using hr i)
    exact ⟨ν,hν,hνa,hνn ▸ hrN.trans hn,fun e => (h1 e).elim,fun _ => hνc.trans_lt hrc⟩

end IntConeFPT.CountPeeling
open IntConeFPT.CountPeeling

private theorem count_cutoff (I : Instance) (hI : I.Valid) (M U : ℕ) (hM : 1 ≤ M)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (hU : 1 ≤ U) (D : IntDesc I) (hD : D.Describes)
    (hDU : D.BoundedBy M U) :
    ((∃ μ, I.Feasible μ) → ∃ μ, I.Feasible μ ∧ I.totalCount μ ≤ Nstar I.τ I.d I.k U) ∧
    ((∃ μ, I.Feasible μ) → (∃ L : ℝ, ∀ μ, I.Feasible μ → L ≤ I.cost μ) →
      ∃ μ, I.Feasible μ ∧ I.totalCount μ ≤ Nstar I.τ I.d I.k U ∧
        ∀ μ', I.Feasible μ' → I.cost μ ≤ I.cost μ') ∧
    ((∃ μ, I.Supported μ ∧ (∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ 0) ∧ I.cost μ < 0) →
      ∃ μ, I.Supported μ ∧ (∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ 0) ∧ I.cost μ < 0 ∧
        I.totalCount μ ≤ Nstar I.τ I.d I.k U) := by
  have comp := compress I hI M U hbox hU D hD hDU
  have feas (v : Mult I) : I.Feasible v ↔ I.Supported v ∧
      ∀ i, D.aggLHS (fun t => I.typeAgg v t) i ≤ D.cW i := by
    exact and_congr_right' (hD.1 (fun t => I.typeAgg v t)).symm
  refine ⟨?_,?_,?_⟩
  · rintro ⟨μ,hμ⟩
    obtain ⟨ν,hs,ha,hN,_,_⟩ := comp D.cW hDU.2.2.2.1 μ hμ.1
      (((feas μ).mp hμ).2) 0 (by intro h; contradiction) (by intro h; contradiction)
    exact ⟨ν,(feas ν).mpr ⟨hs,ha⟩,hN⟩
  · intro hf hb
    obtain ⟨μ,hμ,ho⟩ := exists_global_opt_of_bdd_below I hf hb
    obtain ⟨ν,hs,ha,hN,hc,_⟩ := comp D.cW hDU.2.2.2.1 μ hμ.1 (((feas μ).mp hμ).2) 1
      (fun _ v vs va => ho v ((feas v).mpr ⟨vs,va⟩)) (by intro h; contradiction)
    exact ⟨ν,(feas ν).mpr ⟨hs,ha⟩,hN,fun v hv => (hc rfl).trans (ho v hv)⟩
  · rintro ⟨μ,hs,ha,hc⟩
    obtain ⟨ν,vs,va,hN,_,vn⟩ := comp 0 (by simp) μ hs (by simpa using ha) 2
      (by intro h; contradiction) (fun _ => ⟨rfl,hc⟩)
    exact ⟨ν,vs,by simpa using va,vn rfl,hN⟩


namespace IntConeFPT.Theorem1Reduction

lemma homInstance_zero_feasibleN (I : Instance) (Nmax : ℕ) :
    ∃ μ : Mult (homInstance I), (homInstance I).FeasibleN Nmax μ := by
  refine ⟨0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t
    simp
  · unfold Instance.totalAgg aggr homInstance Instance.Q
    simp [Finsupp.sum_zero_index]
  · unfold Instance.typeAgg aggr count homInstance Instance.A
    simp [Finsupp.sum_zero_index]
  · unfold Instance.totalCount count
    simp [Finsupp.sum_zero_index]

lemma homInstance_Q_iff (I : Instance) (p : (Fin I.d → ℝ) × (Fin I.k → ℝ)) :
    p ∈ (homInstance I).Q ↔ p ∈ I.Qhat := by
  unfold homInstance Instance.Q Instance.Qhat
  simp

lemma homInstance_A_iff (I : Instance) (Y : Fin I.τ → (Fin I.d → ℝ) × (Fin I.k → ℝ) × ℝ) :
    Y ∈ (homInstance I).A ↔ Y ∈ I.Ahat := by
  unfold homInstance Instance.A Instance.Ahat
  simp

lemma costOf_zero {d k : ℕ} (f : (Fin d → ℝ) → ℝ) :
    costOf (d := d) (k := k) f 0 = 0 := by
  simp [costOf]

lemma costOf_add {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (μ₁ μ₂ : Gen d k →₀ ℕ) :
    costOf f (μ₁ + μ₂) = costOf f μ₁ + costOf f μ₂ := by
  unfold costOf
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

lemma costOf_single {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (g : Gen d k) (n : ℕ) :
    costOf f (Finsupp.single g n) = (n : ℝ) * f (fun i => (g.1 i : ℝ)) := by
  unfold costOf
  exact Finsupp.sum_single_index (by simp)

lemma costOf_certList {d k : ℕ} (f : (Fin d → ℝ) → ℝ)
    (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ)) :
    costOf f ((l.map fun c => Finsupp.single (certGen c) c.2.2).sum) =
      ((l.map fun c => (c.2.2 : ℝ) * f (fun i => (c.1 i : ℝ))).sum) := by
  induction l with
  | nil => simp [costOf_zero]
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, costOf_add, costOf_single, ih]
    rfl

lemma ratEvalF_cast_real (I : Instance) (t : Fin I.τ) (x : Fin I.d → ℤ) :
    ((ratEvalF I t x : ℚ) : ℝ) = I.f t (fun i => (x i : ℝ)) := by
  unfold ratEvalF Instance.f
  push_cast
  rfl

lemma ratCertCost_eq_cost (I : Instance) (cert : Cert I) :
    ((ratCertCost I cert : ℚ) : ℝ) = I.cost (certMult I cert) := by
  unfold ratCertCost Instance.cost certMult
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [costOf_certList, Rat.cast_list_sum, List.map_map]
  congr 1
  ext c
  simp [Function.comp_def, ratEvalF_cast_real]

lemma resolveOutput_correct (I : Instance) (hI : I.Valid) (M : ℕ) (hM : 1 ≤ M)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p)
    (o₀ : Output I) (oHom : Output (homInstance I))
    (ho₀ : o₀.CorrectN (Nstar I.τ I.d I.k (coeffBoundU I M)))
    (hoHom : oHom.CorrectN (Nstar I.τ I.d I.k (coeffBoundU I M))) :
    (resolveOutput I o₀ oHom).Correct := by
  obtain ⟨hDesc, hHomLHS, hU1, hBdd, _, _, _, _, _, _, _⟩ := section_3_6_nstar_bound I hI M hM
  obtain ⟨hL15_feas, hL15_opt, hL15_hom⟩ :=
    count_cutoff I hI M (coeffBoundU I M) hM hbox hU1 (clearIntDesc I) hDesc hBdd
  generalize Nstar I.τ I.d I.k (coeffBoundU I M) = N_val at ho₀ hoHom hL15_feas hL15_opt hL15_hom
  cases o₀ with
  | infeasible =>
    simp only [resolveOutput, Output.Correct]
    simp only [Output.CorrectN] at ho₀
    intro hfeas
    exact ho₀ (let ⟨μ, hμ, hcnt⟩ := hL15_feas hfeas; ⟨μ, hμ, hcnt⟩)
  | unbounded =>
    exact False.elim ho₀
  | optimal y₀ v₀ cert₀ =>
    rcases ho₀ with ⟨hOK₀, ⟨hFeas₀, hCnt₀⟩, hAgg₀, hOptN₀⟩
    cases oHom with
    | infeasible =>
      exact False.elim (hoHom (homInstance_zero_feasibleN I N_val))
    | unbounded =>
      exact False.elim hoHom
    | optimal yHom vHom certHom =>
      rcases hoHom with ⟨_, ⟨⟨hSuppHom, hQHom, hAHom⟩, _⟩, _, hOptNHom⟩
      let certHomI : Cert I := certHom
      have hCertEq : certMult (homInstance I) certHom = certMult I certHomI := rfl
      have hSuppI : I.Supported (certMult I certHomI) := hSuppHom
      have hQI : I.totalAgg (certMult I certHomI) ∈ (homInstance I).Q := hQHom
      have hAI : (fun t => I.typeAgg (certMult I certHomI) t) ∈ (homInstance I).A := hAHom
      simp only [resolveOutput]
      split_ifs with hneg
      · simp only [Output.Correct]
        have hcost_neg : I.cost (certMult I certHomI) < 0 := by
          rw [← ratCertCost_eq_cost I certHomI]
          exact_mod_cast hneg
        refine (section_B3_unboundedness I hI ⟨certMult I cert₀, hFeas₀⟩).mpr ?_
        exact ⟨certMult I certHomI, hSuppI, (homInstance_Q_iff I _).mp hQI,
          (homInstance_A_iff I _).mp hAI, hcost_neg⟩
      · simp only [Output.Correct]
        refine ⟨hOK₀, hFeas₀, hAgg₀, ?_⟩
        have hcost_nonneg : 0 ≤ I.cost (certMult I certHomI) := by
          rw [← ratCertCost_eq_cost I certHomI]
          have : (0 : ℚ) ≤ ratCertCost I certHomI := not_lt.mp hneg
          exact_mod_cast this
        have hNotUnb : ¬ I.Unbounded := by
          intro hUnb
          obtain ⟨μ, hSupp, hQhat, hAhat, hlt⟩ :=
            (section_B3_unboundedness I hI ⟨certMult I cert₀, hFeas₀⟩).mp hUnb
          have hLHS : ∀ i, (clearIntDesc I).aggLHS (fun t => I.typeAgg μ t) i ≤ 0 :=
            (hHomLHS (fun t => I.typeAgg μ t)).mpr ⟨hQhat, hAhat⟩
          obtain ⟨μ₁, hSupp₁, hLHS₁, hlt₁, hCnt₁⟩ := hL15_hom ⟨μ, hSupp, hLHS, hlt⟩
          obtain ⟨hQhat₁, hAhat₁⟩ := (hHomLHS (fun t => I.typeAgg μ₁ t)).mp hLHS₁
          have hFeasHom₁ : (homInstance I).FeasibleN N_val μ₁ :=
            ⟨⟨hSupp₁, (homInstance_Q_iff I _).mpr hQhat₁, (homInstance_A_iff I _).mpr hAhat₁⟩,
              hCnt₁⟩
          have hle : I.cost (certMult I certHomI) ≤ I.cost μ₁ := hOptNHom μ₁ hFeasHom₁
          linarith
        have hBoundedBelow : ∃ B : ℝ, ∀ μ, I.Feasible μ → B ≤ I.cost μ := by
          by_contra hNoB
          apply hNotUnb
          intro B
          by_contra hAllGe
          apply hNoB
          refine ⟨B, fun μ hμ => ?_⟩
          by_contra hlt
          exact hAllGe ⟨μ, hμ, lt_of_not_ge hlt⟩
        obtain ⟨B, hB⟩ := hBoundedBelow
        obtain ⟨μ_star, hFeas_star, hCnt_star, hGlob_star⟩ :=
          hL15_opt ⟨certMult I cert₀, hFeas₀⟩ ⟨B, hB⟩
        intro μ' hμ'
        exact le_trans (hOptN₀ μ_star ⟨hFeas_star, hCnt_star⟩) (hGlob_star μ' hμ')

lemma RunsWithin.mono {M : Machine} {inp out : List Sym} {T₁ T₂ : ℝ}
    (h : RunsWithin M inp out T₁) (hle : T₁ ≤ T₂) : RunsWithin M inp out T₂ := by
  rcases h with ⟨m, hm, hrun⟩
  exact ⟨m, le_trans hm hle, hrun⟩

lemma one_le_tau_logb {τ : ℕ} (hτ : 1 ≤ τ) :
    (1 : ℝ) ≤ (τ : ℝ) * Real.logb 2 ((τ : ℝ) + 1) := by
  have hτR : (1 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ
  have hlog : (1 : ℝ) ≤ Real.logb 2 ((τ : ℝ) + 1) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by linarith)]
    linarith [Real.rpow_one (2 : ℝ)]
  nlinarith

lemma nat_le_two_rpow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ (n : ℝ) := by
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self

lemma fptBound_mono_L {C τ d L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    fptBound C τ d L₁ ≤ fptBound C τ d L₂ := by
  unfold fptBound
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hL) C

lemma fptBound_nonneg (C τ d L : ℕ) : 0 ≤ fptBound C τ d L := by
  unfold fptBound
  positivity

lemma exp_factor_bound {C_p14 C_drv k₁ C d : ℕ} {α : ℝ}
    (hd1 : 1 ≤ d) (hα1 : 1 ≤ α) (hC : C_p14 + C_drv + k₁ + 4 ≤ C) :
    ((2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))) ^ C_drv * (2 : ℝ) ^ (k₁ * d) ≤
      (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C : ℝ) * d)) := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hα1
  have hdR : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := le_trans zero_le_one hdR
  have hF_pow : ((2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))) ^ C_drv =
      (2 : ℝ) ^ ((C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have h2_pow : ((2 : ℝ) ^ (k₁ * d)) = (2 : ℝ) ^ (((k₁ * d : ℕ) : ℝ)) :=
    (Real.rpow_natCast 2 (k₁ * d)).symm
  rw [hF_pow, h2_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hd_le_2d : (d : ℝ) ≤ (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) := by
    calc (d : ℝ) ≤ (2 : ℝ) ^ (d : ℝ) := nat_le_two_rpow d
      _ ≤ (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          calc (d : ℝ) = 1 * (d : ℝ) := (one_mul _).symm
            _ ≤ ((C_p14 : ℝ) + 1) * (d : ℝ) :=
                mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) C_p14]) hd0
  have h2d_mono : (2 : ℝ) ^ ((C_p14 : ℝ) * d) ≤ (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hd0
  have hKd : ((k₁ * d : ℕ) : ℝ) ≤ α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := by
    calc ((k₁ * d : ℕ) : ℝ) = 1 * ((k₁ : ℝ) * (d : ℝ)) := by push_cast; ring
      _ ≤ α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) :=
          mul_le_mul hα1 (mul_le_mul_of_nonneg_left hd_le_2d (Nat.cast_nonneg _))
            (by positivity) hα0
  have hCd : (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d)) ≤
      α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := by
    calc (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))
      _ = ((C_drv : ℝ) * α) * (2 : ℝ) ^ ((C_p14 : ℝ) * d) := by ring
      _ ≤ ((C_drv : ℝ) * α) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) :=
          mul_le_mul_of_nonneg_left h2d_mono (mul_nonneg (Nat.cast_nonneg _) hα0)
      _ = α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := by ring
  have hCoef : (C_drv : ℝ) + (k₁ : ℝ) ≤ (2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) := by
    have h := nat_le_two_rpow (C_drv + k₁ + 1)
    have hcast : ((C_drv + k₁ + 1 : ℕ) : ℝ) = (C_drv : ℝ) + (k₁ : ℝ) + 1 := by push_cast; ring
    linarith
  have hExpC : (2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) ≤
      (2 : ℝ) ^ ((C : ℝ) * d) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hC_geR : ((C_p14 + C_drv + k₁ + 4 : ℕ) : ℝ) ≤ (C : ℝ) := Nat.cast_le.mpr hC
    have hcast1 : ((C_drv + k₁ + 1 : ℕ) : ℝ) = (C_drv : ℝ) + (k₁ : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((C_p14 + C_drv + k₁ + 4 : ℕ) : ℝ) =
        (C_p14 : ℝ) + (C_drv : ℝ) + (k₁ : ℝ) + 4 := by push_cast; ring
    rw [hcast1]
    rw [hcast2] at hC_geR
    have h1d : ((C_drv : ℝ) + (k₁ : ℝ) + 1) ≤ ((C_drv : ℝ) + (k₁ : ℝ) + 1) * (d : ℝ) :=
      le_mul_of_one_le_right (by positivity) hdR
    calc ((C_drv : ℝ) + (k₁ : ℝ) + 1) + ((C_p14 : ℝ) + 1) * (d : ℝ)
      _ ≤ ((C_drv : ℝ) + (k₁ : ℝ) + 1) * (d : ℝ) + ((C_p14 : ℝ) + 1) * (d : ℝ) := by linarith [h1d]
      _ = ((C_p14 : ℝ) + (C_drv : ℝ) + (k₁ : ℝ) + 2) * (d : ℝ) := by ring
      _ ≤ (C : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hd0
  calc (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d)) + ((k₁ * d : ℕ) : ℝ)
    _ ≤ α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) +
          α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := add_le_add hCd hKd
    _ = α * (((C_drv : ℝ) + (k₁ : ℝ)) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := by ring
    _ ≤ α * ((2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCoef (by positivity)) hα0
    _ ≤ α * (2 : ℝ) ^ ((C : ℝ) * d) :=
        mul_le_mul_of_nonneg_left hExpC hα0

lemma fptBound_absorb (C_box C_p14 C_drv : ℕ) :
    ∃ C : ℕ, ∀ {τ d L LM LN L₀ LHom : ℕ},
      1 ≤ d → 1 ≤ τ → 1 ≤ L → τ ≤ L →
      LM ≤ L ^ C_box →
      LN ≤ 64 * (τ * 2 ^ d) ^ 3 * (L + LM) ^ 2 →
      L₀ = L + LN + 1 →
      LHom ≤ L₀ →
      (((L + LM + LN +
          (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2 : ℝ)) ^ C_drv) ≤
        fptBound C τ d L := by
  set E₁ : ℕ := 2 * C_box + 5
  set E₂ : ℕ := E₁ * (C_p14 + 1)
  set K₁ : ℕ := (12 * C_p14 + 15) * (C_drv + 1)
  set C : ℕ := max (E₂ * C_drv) (C_p14 + C_drv + K₁ + 4)
  refine ⟨C, fun {τ d L LM LN L₀ LHom} hd1 hτ1 hL1 hτL hMlen hNlen hL₀_eq hLHom_le => ?_⟩
  have hE₁_ge1 : 1 ≤ E₁ := by omega
  have hE₂_ge1 : 1 ≤ E₂ := Nat.mul_pos hE₁_ge1 (Nat.succ_pos _)
  have hE₂_ge_box : C_box ≤ E₂ := by
    calc C_box ≤ E₁ := by omega
      _ = E₁ * 1 := (Nat.mul_one E₁).symm
      _ ≤ E₁ * (C_p14 + 1) := Nat.mul_le_mul_left E₁ (Nat.succ_pos _)
  have hE₂_ge_E₁ : E₁ ≤ E₂ := by
    calc E₁ = E₁ * 1 := (Nat.mul_one E₁).symm
      _ ≤ E₁ * (C_p14 + 1) := Nat.mul_le_mul_left E₁ (Nat.succ_pos _)
  have hE₂_ge_mul : E₁ * C_p14 ≤ E₂ :=
    Nat.mul_le_mul_left E₁ (Nat.le_succ C_p14)
  have hLN_bound : LN ≤ 2 ^ (3 * d + 8) * L ^ E₁ := by
    have hL_pow1 : L ≤ L ^ (C_box + 1) := by
      simpa using Nat.pow_le_pow_right hL1 (Nat.le_add_left 1 C_box)
    have hM_pow : LM ≤ L ^ (C_box + 1) :=
      le_trans hMlen (Nat.pow_le_pow_right hL1 (Nat.le_succ C_box))
    have hsum_sq : (L + LM) ^ 2 ≤ 4 * L ^ (2 * C_box + 2) := by
      calc (L + LM) ^ 2
        _ ≤ (2 * L ^ (C_box + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * L ^ (2 * C_box + 2) := by ring
    have hs3 : (τ * 2 ^ d) ^ 3 ≤ L ^ 3 * 2 ^ (3 * d) := by
      calc (τ * 2 ^ d) ^ 3 = τ ^ 3 * 2 ^ (3 * d) := by ring
        _ ≤ L ^ 3 * 2 ^ (3 * d) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hτL 3)
    calc LN
      _ ≤ 64 * (τ * 2 ^ d) ^ 3 * (L + LM) ^ 2 := hNlen
      _ ≤ 64 * (L ^ 3 * 2 ^ (3 * d)) * (4 * L ^ (2 * C_box + 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 64 hs3) hsum_sq
      _ = 2 ^ (3 * d + 8) * L ^ E₁ := by
          have h64 : (64 : ℕ) * 4 = 2 ^ 8 := by decide
          calc 64 * (L ^ 3 * 2 ^ (3 * d)) * (4 * L ^ (2 * C_box + 2))
            _ = (2 ^ (3 * d) * (64 * 4)) * (L ^ 3 * L ^ (2 * C_box + 2)) := by ring
            _ = 2 ^ (3 * d + 8) * L ^ E₁ := by
                rw [h64, ← pow_add, ← pow_add]
                congr 2
                omega
  have hL₀_len : L₀ ≤ 2 ^ (3 * d + 9) * L ^ E₁ := by
    have hLE1 : L + 1 ≤ 2 * L ^ E₁ := by
      have : 1 ≤ L ^ E₁ := Nat.one_le_pow E₁ L hL1
      have : L ≤ L ^ E₁ := by simpa using Nat.pow_le_pow_right hL1 hE₁_ge1
      omega
    have h2pos : 2 ≤ 2 ^ (3 * d + 8) :=
      le_trans (by decide) (Nat.pow_le_pow_right (by omega) (by omega) : 2 ^ 1 ≤ 2 ^ (3 * d + 8))
    have hp9 : 2 ^ (3 * d + 9) = 2 * 2 ^ (3 * d + 8) := by
      rw [show 3 * d + 9 = (3 * d + 8) + 1 by omega, pow_succ, mul_comm]
    rw [hL₀_eq, hp9]
    nlinarith
  set α : ℝ := (τ : ℝ) * Real.logb 2 ((τ : ℝ) + 1)
  have hα1 : 1 ≤ α := one_le_tau_logb hτ1
  have hα0 : 0 ≤ α := by linarith
  set F₀ : ℝ := (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))
  have hF₀1 : 1 ≤ F₀ := Real.one_le_rpow (by norm_num) (by positivity)
  have hF₀0 : 0 ≤ F₀ := by linarith
  have hT₀_bound : fptBound C_p14 τ d L₀ ≤
      F₀ * (2 : ℝ) ^ ((3 * d + 9) * C_p14) * (L : ℝ) ^ (E₁ * C_p14) := by
    calc fptBound C_p14 τ d L₀
      _ ≤ fptBound C_p14 τ d (2 ^ (3 * d + 9) * L ^ E₁) := fptBound_mono_L hL₀_len
      _ = F₀ * (2 : ℝ) ^ ((3 * d + 9) * C_p14) * (L : ℝ) ^ (E₁ * C_p14) := by
          unfold fptBound
          have hpow : ((2 ^ (3 * d + 9) * L ^ E₁ : ℕ) : ℝ) ^ C_p14 =
              (2 : ℝ) ^ ((3 * d + 9) * C_p14) * (L : ℝ) ^ (E₁ * C_p14) := by
            push_cast
            rw [mul_pow, ← pow_mul, ← pow_mul]
          rw [hpow]
          ring
  have hThom_bound : fptBound C_p14 τ d LHom ≤
      F₀ * (2 : ℝ) ^ ((3 * d + 9) * C_p14) * (L : ℝ) ^ (E₁ * C_p14) :=
    le_trans (fptBound_mono_L hLHom_le) hT₀_bound
  have hLR1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLE2_ge : ∀ e ≤ E₂, (L : ℝ) ^ e ≤ (L : ℝ) ^ E₂ :=
    fun e he => pow_le_pow_right₀ hLR1 he
  set P₂ : ℕ := (12 * C_p14 + 12) * d
  have hP₂_ge1 : (3 * d + 9) * C_p14 ≤ P₂ := by
    have hCd : C_p14 ≤ C_p14 * d := Nat.le_mul_of_pos_right C_p14 hd1
    calc (3 * d + 9) * C_p14 = 3 * (C_p14 * d) + 9 * C_p14 := by ring
      _ ≤ 3 * (C_p14 * d) + 9 * (C_p14 * d) := Nat.add_le_add_left (Nat.mul_le_mul_left 9 hCd) _
      _ = (12 * C_p14) * d := by ring
      _ ≤ (12 * C_p14 + 12) * d := Nat.mul_le_mul_right d (Nat.le_add_right _ 12)
  have hP₂_ge2 : 3 * d + 8 ≤ P₂ := by
    calc 3 * d + 8 ≤ 12 * d := by omega
      _ ≤ (12 * C_p14 + 12) * d := Nat.mul_le_mul_right d (by omega)
  set B_unit : ℝ := F₀ * (2 : ℝ) ^ P₂ * (L : ℝ) ^ E₂
  have hUnit_ge : (1 : ℝ) ≤ F₀ * (2 : ℝ) ^ P₂ :=
    one_le_mul_of_one_le_of_one_le hF₀1 (one_le_pow₀ (by norm_num))
  have ht1 : (L : ℝ) ≤ B_unit := by
    calc (L : ℝ) = 1 * (L : ℝ) ^ 1 := by ring
      _ ≤ (F₀ * (2 : ℝ) ^ P₂) * (L : ℝ) ^ E₂ :=
          mul_le_mul hUnit_ge (hLE2_ge 1 hE₂_ge1) (by positivity) (by positivity)
      _ = B_unit := by ring
  have ht2 : (LM : ℝ) ≤ B_unit := by
    have h1 : (LM : ℝ) ≤ (L : ℝ) ^ C_box := by exact_mod_cast hMlen
    calc (LM : ℝ) ≤ 1 * (L : ℝ) ^ C_box := by linarith
      _ ≤ (F₀ * (2 : ℝ) ^ P₂) * (L : ℝ) ^ E₂ :=
          mul_le_mul hUnit_ge (hLE2_ge C_box hE₂_ge_box) (by positivity) (by positivity)
      _ = B_unit := by ring
  have ht3 : (LN : ℝ) ≤ B_unit := by
    have h1 : (LN : ℝ) ≤ (2 : ℝ) ^ (3 * d + 8) * (L : ℝ) ^ E₁ := by exact_mod_cast hLN_bound
    have h2 : (2 : ℝ) ^ (3 * d + 8) ≤ F₀ * (2 : ℝ) ^ P₂ := by
      calc (2 : ℝ) ^ (3 * d + 8) = 1 * (2 : ℝ) ^ (3 * d + 8) := by ring
        _ ≤ F₀ * (2 : ℝ) ^ P₂ :=
            mul_le_mul hF₀1 (pow_le_pow_right₀ (by norm_num) hP₂_ge2) (by positivity) hF₀0
    exact le_trans h1 (mul_le_mul h2 (hLE2_ge E₁ hE₂_ge_E₁) (by positivity) (by positivity))
  have ht4 : (L : ℝ) ^ C_box ≤ B_unit := by
    calc (L : ℝ) ^ C_box = 1 * (L : ℝ) ^ C_box := by ring
      _ ≤ (F₀ * (2 : ℝ) ^ P₂) * (L : ℝ) ^ E₂ :=
          mul_le_mul hUnit_ge (hLE2_ge C_box hE₂_ge_box) (by positivity) (by positivity)
      _ = B_unit := by ring
  have ht5 : fptBound C_p14 τ d L₀ ≤ B_unit := by
    refine le_trans hT₀_bound ?_
    refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hP₂_ge1) hF₀0)
      (hLE2_ge (E₁ * C_p14) hE₂_ge_mul) (by positivity) (by positivity)
  have ht6 : fptBound C_p14 τ d LHom ≤ B_unit :=
    le_trans (fptBound_mono_L hLHom_le) ht5
  have ht7 : (2 : ℝ) ≤ 2 * B_unit := by
    have : (1 : ℝ) ≤ B_unit :=
      one_le_mul_of_one_le_of_one_le hUnit_ge (one_le_pow₀ hLR1)
    linarith
  have hBase : ((L : ℝ) + (LM : ℝ) + (LN : ℝ) +
      (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2) ≤ 8 * B_unit := by
    linarith
  have h8B : 8 * B_unit ≤ F₀ * (2 : ℝ) ^ ((12 * C_p14 + 15) * d) * (L : ℝ) ^ E₂ := by
    have h3d : P₂ + 3 ≤ (12 * C_p14 + 15) * d := by
      calc P₂ + 3 = (12 * C_p14 + 12) * d + 3 := rfl
        _ ≤ (12 * C_p14 + 12) * d + 3 * d := Nat.add_le_add_left (by omega) _
        _ = (12 * C_p14 + 15) * d := by ring
    calc 8 * B_unit = F₀ * ((2 : ℝ) ^ P₂ * (2 : ℝ) ^ 3) * (L : ℝ) ^ E₂ := by
          change 8 * (F₀ * (2 : ℝ) ^ P₂ * (L : ℝ) ^ E₂) = _
          ring
      _ = F₀ * (2 : ℝ) ^ (P₂ + 3) * (L : ℝ) ^ E₂ := by rw [← pow_add]
      _ ≤ F₀ * (2 : ℝ) ^ ((12 * C_p14 + 15) * d) * (L : ℝ) ^ E₂ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h3d) hF₀0)
            (by positivity)
  have hPow : ((L : ℝ) + (LM : ℝ) + (LN : ℝ) +
      (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2) ^ C_drv ≤
      F₀ ^ C_drv * (2 : ℝ) ^ (K₁ * d) * (L : ℝ) ^ (E₂ * C_drv) := by
    have hK₁_ge : ((12 * C_p14 + 15) * d) * C_drv ≤ K₁ * d := by
      calc ((12 * C_p14 + 15) * d) * C_drv
        _ = ((12 * C_p14 + 15) * C_drv) * d := by ring
        _ ≤ ((12 * C_p14 + 15) * (C_drv + 1)) * d :=
            Nat.mul_le_mul_right d (Nat.mul_le_mul_left _ (Nat.le_succ C_drv))
    have hLHS0 : 0 ≤ ((L : ℝ) + (LM : ℝ) + (LN : ℝ) +
        (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2) :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg
              (add_nonneg (add_nonneg (by positivity) (by positivity)) (by positivity))
              (by positivity))
            (fptBound_nonneg C_p14 τ d L₀))
          (fptBound_nonneg C_p14 τ d LHom))
        (by positivity)
    calc _ ≤ (F₀ * (2 : ℝ) ^ ((12 * C_p14 + 15) * d) * (L : ℝ) ^ E₂) ^ C_drv :=
          pow_le_pow_left₀ hLHS0 (le_trans hBase h8B) C_drv
      _ = F₀ ^ C_drv * (2 : ℝ) ^ (((12 * C_p14 + 15) * d) * C_drv) * (L : ℝ) ^ (E₂ * C_drv) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ F₀ ^ C_drv * (2 : ℝ) ^ (K₁ * d) * (L : ℝ) ^ (E₂ * C_drv) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hK₁_ge) (by positivity))
            (by positivity)
  have hC_ge_left : E₂ * C_drv ≤ C := le_max_left _ _
  have hC_ge_right : C_p14 + C_drv + K₁ + 4 ≤ C := le_max_right _ _
  have hExpFactor : F₀ ^ C_drv * (2 : ℝ) ^ (K₁ * d) ≤
      (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C : ℝ) * d)) :=
    exp_factor_bound hd1 hα1 hC_ge_right
  have hLPow : (L : ℝ) ^ (E₂ * C_drv) ≤ (L : ℝ) ^ C :=
    pow_le_pow_right₀ hLR1 hC_ge_left
  refine le_trans hPow ?_
  unfold fptBound
  exact mul_le_mul hExpFactor hLPow (by positivity) (by positivity)

lemma hlen_app3 (l₁ l₂ : List Sym) :
    (l₁ ++ l₂ ++ [3]).length = l₁.length + l₂.length + 1 := by
  simp only [List.length_append, List.length_singleton]

lemma hlen_app3_mono {l₁ l₁' l₂ : List Sym} (h : l₁.length ≤ l₁'.length) :
    (l₁ ++ l₂ ++ [3]).length ≤ (l₁' ++ l₂ ++ [3]).length := by
  simp only [List.length_append]
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

lemma main_step (C_box C_p14 C_drv C : ℕ) (M_box M_p14 M_main : Machine)
    (hBox : ∀ I : Instance, I.Valid →
      ∃ M : ℕ, 1 ≤ M ∧ (∀ t, ∀ p ∈ I.P t, InBox M p) ∧
        (encNat M).length ≤ (encInstance I).length ^ C_box ∧
        RunsWithin M_box (encInstance I) (encNat M) (((encInstance I).length : ℝ) ^ C_box))
    (hP14 : ∀ I : Instance, I.Valid → ∀ Nmax : ℕ,
      let inp := encInstance I ++ encNat Nmax ++ [3]
      ∃ o : Output I, o.CorrectN Nmax ∧
        RunsWithin M_p14 inp (encOutput o) (fptBound C_p14 I.τ I.d inp.length))
    (hDrv : ∀ (I : Instance), I.Valid →
      ∀ (M : ℕ), 1 ≤ M →
      ∀ (o₀ : Output I) (oHom : Output (homInstance I)) (T_box T₀ T_hom : ℝ),
        0 ≤ T_box → 0 ≤ T₀ → 0 ≤ T_hom →
        let N_star := Nstar I.τ I.d I.k (coeffBoundU I M)
        RunsWithin M_box (encInstance I) (encNat M) T_box →
        RunsWithin M_p14 (encInstance I ++ encNat N_star ++ [3]) (encOutput o₀) T₀ →
        RunsWithin M_p14 (encInstance (homInstance I) ++ encNat N_star ++ [3]) (encOutput oHom) T_hom →
        RunsWithin M_main (encInstance I) (encOutput (resolveOutput I o₀ oHom))
          (((encInstance I).length + (encNat M).length + (encNat N_star).length +
            T_box + T₀ + T_hom + 2 : ℝ) ^ C_drv))
    (hAbsorb : ∀ {τ d L LM LN L₀ LHom : ℕ},
      1 ≤ d → 1 ≤ τ → 1 ≤ L → τ ≤ L →
      LM ≤ L ^ C_box →
      LN ≤ 64 * (τ * 2 ^ d) ^ 3 * (L + LM) ^ 2 →
      L₀ = L + LN + 1 →
      LHom ≤ L₀ →
      (((L + LM + LN +
          (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2 : ℝ)) ^ C_drv) ≤
        fptBound C τ d L)
    (I : Instance) (hI : I.Valid) :
    ∃ o : Output I, o.Correct ∧
      RunsWithin M_main (encInstance I) (encOutput o) (fptBound C I.τ I.d (encInstance I).length) := by
  obtain ⟨M_val, hM1, hInBox, hMlen, hRunBox⟩ := hBox I hI
  obtain ⟨_, _, _, _, hHomValid, hHomLen, hL1, _, _, hτL, hNlen⟩ :=
    section_3_6_nstar_bound I hI M_val hM1
  let N_val : ℕ := Nstar I.τ I.d I.k (coeffBoundU I M_val)
  change (encNat N_val).length ≤ _ at hNlen
  obtain ⟨o₀, hCorr₀, hRun₀⟩ := hP14 I hI N_val
  obtain ⟨oHom, hCorrHom, hRunHom⟩ := hP14 (homInstance I) hHomValid N_val
  have hCorrOut : (resolveOutput I o₀ oHom).Correct :=
    resolveOutput_correct I hI M_val hM1 hInBox o₀ oHom hCorr₀ hCorrHom
  have hTbox0 : (0 : ℝ) ≤ ((encInstance I).length : ℝ) ^ C_box :=
    pow_nonneg (Nat.cast_nonneg _) _
  have hT₀0 : (0 : ℝ) ≤ fptBound C_p14 I.τ I.d (encInstance I ++ encNat N_val ++ [3]).length :=
    fptBound_nonneg _ _ _ _
  have hThom0 : (0 : ℝ) ≤
      fptBound C_p14 I.τ I.d (encInstance (homInstance I) ++ encNat N_val ++ [3]).length :=
    fptBound_nonneg _ _ _ _
  have hτ_eq : (homInstance I).τ = I.τ := rfl
  have hd_eq : (homInstance I).d = I.d := rfl
  rw [hτ_eq, hd_eq] at hRunHom
  have hRunMain := hDrv I hI M_val hM1 o₀ oHom
    (((encInstance I).length : ℝ) ^ C_box)
    (fptBound C_p14 I.τ I.d (encInstance I ++ encNat N_val ++ [3]).length)
    (fptBound C_p14 I.τ I.d (encInstance (homInstance I) ++ encNat N_val ++ [3]).length)
    hTbox0 hT₀0 hThom0 hRunBox hRun₀ hRunHom
  have hL₀_eq : (encInstance I ++ encNat N_val ++ [3]).length =
      (encInstance I).length + (encNat N_val).length + 1 :=
    hlen_app3 (encInstance I) (encNat N_val)
  have hLHom_le : (encInstance (homInstance I) ++ encNat N_val ++ [3]).length ≤
      (encInstance I ++ encNat N_val ++ [3]).length :=
    hlen_app3_mono hHomLen
  exact ⟨resolveOutput I o₀ oHom, hCorrOut,
    RunsWithin.mono hRunMain (hAbsorb hI.one_le_d hI.one_le_τ hL1 hτL hMlen hNlen hL₀_eq hLHom_le)⟩

end IntConeFPT.Theorem1Reduction

open IntConeFPT
open IntConeFPT.Theorem1Reduction

theorem solution :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∃ o : Output I, o.Correct ∧
        RunsWithin M (encInstance I) (encOutput o) (fptBound C I.τ I.d (encInstance I).length) := by
  rcases linear_box_bound with ⟨C_box, M_box, hBox⟩
  rcases proposition_14 with ⟨C_p14, M_p14, hP14⟩
  rcases section_3_6_driver M_box M_p14 with ⟨C_drv, M_main, hDrv⟩
  rcases fptBound_absorb C_box C_p14 C_drv with ⟨C, hAbsorb⟩
  exact ⟨C, M_main, main_step C_box C_p14 C_drv C M_box M_p14 M_main hBox hP14 hDrv hAbsorb⟩
