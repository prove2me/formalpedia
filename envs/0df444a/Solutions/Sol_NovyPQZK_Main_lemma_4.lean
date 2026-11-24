-- Prove2me | solution 1 for NovyPQZK.Main.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T19:46:43.061202+00:00
-- url     : https://prove2.me/submissions/6c8c5b38-db16-4836-9bd8-2a0ea0f20467

import Mathlib
import Definitions.Def_NovyPQZK_Main_Binding

namespace NovyPQZK.Main

open QAlgorithms
open scoped Matrix

/-! ## Generic algebra of `embedOp`, permutation matrices, and fresh ancillas -/

/-- The permutation matrix of `φ` on basis states. -/
def permOf {N : ℕ} (φ : Qubits N → Qubits N) : Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.of fun y z => if y = φ z then 1 else 0

theorem permOf_mul {N : ℕ} (φ ψ : Qubits N → Qubits N) :
    permOf φ * permOf ψ = permOf (φ ∘ ψ) := by
  ext y z
  simp only [permOf, Matrix.mul_apply, Matrix.of_apply, Function.comp_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (ψ z)]
  simp

theorem permOf_id {N : ℕ} : permOf (N := N) id = 1 := by
  ext y z
  simp [permOf, Matrix.one_apply]

theorem permOf_conjTranspose {N : ℕ} (φ : Qubits N → Qubits N) (hφ : ∀ z, φ (φ z) = z) :
    (permOf φ)ᴴ = permOf φ := by
  ext y z
  simp only [permOf, Matrix.conjTranspose_apply, Matrix.of_apply]
  have : (z = φ y) ↔ (y = φ z) := ⟨fun h => by rw [h, hφ], fun h => by rw [h, hφ]⟩
  by_cases h : y = φ z
  · rw [if_pos (this.2 h), if_pos h]; simp
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]; simp

theorem permOf_conj_apply {N : ℕ} (φ : Qubits N → Qubits N) (hφ : ∀ z, φ (φ z) = z)
    (M : Matrix (Qubits N) (Qubits N) ℂ) (y z : Qubits N) :
    (permOf φ * M * (permOf φ)ᴴ) y z = M (φ y) (φ z) := by
  rw [permOf_conjTranspose φ hφ, Matrix.mul_apply]
  have h1 : ∀ x, (permOf φ * M) y x = M (φ y) x := by
    intro x
    rw [Matrix.mul_apply]
    have : ∀ w, permOf φ y w * M w x = if w = φ y then M (φ y) x else 0 := by
      intro w
      simp only [permOf, Matrix.of_apply]
      by_cases hw : w = φ y
      · subst hw; rw [if_pos (hφ y).symm, if_pos rfl, one_mul]
      · rw [if_neg hw, if_neg (fun h => hw (by rw [h, hφ])), zero_mul]
    simp_rw [this]
    simp
  simp_rw [h1]
  simp only [permOf, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  simp

theorem permOf_unitary {N : ℕ} (φ : Qubits N → Qubits N) (hφ : ∀ z, φ (φ z) = z) :
    permOf φ ∈ Matrix.unitaryGroup (Qubits N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, permOf_conjTranspose φ hφ,
    permOf_mul]
  have : φ ∘ φ = id := funext hφ
  rw [this, permOf_id]

theorem embedOp_mul {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
          (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x : Qubits n,
          if ∀ a : Fin n, a ∉ Set.range w → y a = x a then
            A (y ∘ w) (x ∘ w) * B (x ∘ w) (z ∘ w) else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · have hxz : ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun a ha =>
          (hyx a ha).symm.trans (hyz a ha)
        rw [if_pos hyx, if_pos hxz, if_pos hyx]
      · rw [if_neg hyx, zero_mul, if_neg hyx]
    rw [hsum, ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun x _ => x ∘ w)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ hx₁ x₂ hx₂ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨b, rfl⟩
          exact congrFun h b
        · exact (hx₁ a ha).symm.trans (hx₂ a ha))
      (fun x' _ => by
        refine ⟨fun a => if h : ∃ b : Fin m, w b = a then x' (Classical.choose h) else y a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha
          have hnot : ¬ ∃ b : Fin m, w b = a := by simpa [Set.mem_range] using ha
          simp [hnot]
        · funext b
          have h : ∃ b' : Fin m, w b' = w b := ⟨b, rfl⟩
          simp only [Function.comp_apply, h, ↓reduceDIte]
          exact congrArg x' (w.injective (Classical.choose_spec h)))
      (fun _ _ => rfl)
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have hxz : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz (fun a ha => (hyx a ha).trans (hxz a ha))
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

theorem embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (u : Fin k ↪ Fin m) (w : Fin m ↪ Fin n) :
    embedOp (embedOp M u) w = embedOp M (u.trans w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hR : ∀ a : Fin n, a ∉ Set.range (u.trans w) → y a = z a
  · rw [if_pos hR]
    have hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a := by
      intro a ha
      apply hR a
      rintro ⟨c, hc⟩
      exact ha ⟨u c, hc⟩
    have hu : ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b) := by
      intro b hb
      apply hR (w b)
      rintro ⟨c, hc⟩
      exact hb ⟨c, w.injective hc⟩
    rw [if_pos hw]
    change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
      then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = _
    rw [if_pos hu]
  · rw [if_neg hR]
    simp only [not_forall] at hR
    rcases hR with ⟨a, ha, hne⟩
    by_cases haw : a ∈ Set.range w
    · rcases haw with ⟨b, rfl⟩
      have hbu : b ∉ Set.range u := by
        rintro ⟨c, rfl⟩
        exact ha ⟨c, rfl⟩
      by_cases hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a
      · rw [if_pos hw]
        change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
          then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = 0
        rw [if_neg (fun hu => hne (hu b hbu))]
      · rw [if_neg hw]
    · rw [if_neg (fun hw => hne (hw a haw))]

theorem embedOp_conjTranspose {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    (embedOp M w)ᴴ = embedOp Mᴴ w := by
  ext y z
  simp only [embedOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  have : (∀ a : Fin n, a ∉ Set.range w → z a = y a) ↔ (∀ a : Fin n, a ∉ Set.range w → y a = z a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h, star_zero]

theorem circuit_unitary_cons {N : ℕ} (g : GateApp allSmallGates N) (c : QCircuit N) :
    Circuit.unitary (g :: c) = Circuit.unitary c * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary, List.reverse_cons, List.prod_append]

theorem circuit_unitary_append {N : ℕ} (c₁ c₂ : QCircuit N) :
    Circuit.unitary (c₁ ++ c₂) = Circuit.unitary c₂ * Circuit.unitary c₁ := by
  simp [Circuit.unitary, List.reverse_append, List.prod_append]

theorem circuit_unitary_nil {N : ℕ} : Circuit.unitary ([] : QCircuit N) = 1 := by
  simp [Circuit.unitary]

/-! ### The register with `m` fresh wires appended -/

section Lift
variable {N m N' : ℕ}

/-- The old wires inside the enlarged register. -/
def eL (h : N + m = N') : Fin N ↪ Fin N' :=
  ⟨fun i => ⟨i.val, by omega⟩, fun a b hab => by simpa [Fin.ext_iff] using hab⟩

/-- The fresh wires. -/
def fL (h : N + m = N') (j : Fin m) : Fin N' := ⟨N + j.val, by omega⟩

theorem eL_val (h : N + m = N') (i : Fin N) : (eL h i).val = i.val := rfl
theorem fL_val (h : N + m = N') (j : Fin m) : (fL h j).val = N + j.val := rfl

theorem eL_ne_fL (h : N + m = N') (i : Fin N) (j : Fin m) : eL h i ≠ fL h j := by
  intro hh; have := congrArg Fin.val hh; simp [eL_val, fL_val] at this; omega

/-- Splitting a basis state of the enlarged register. -/
def splitQ (h : N + m = N') : Qubits N' ≃ Qubits N × Qubits m where
  toFun z := (z ∘ eL h, z ∘ fL h)
  invFun p a := if ha : a.val < N then p.1 ⟨a.val, ha⟩ else p.2 ⟨a.val - N, by omega⟩
  left_inv z := by
    funext a
    by_cases ha : a.val < N
    · simp only [ha, ↓reduceDIte, Function.comp_apply]
      congr 1
    · simp only [ha, ↓reduceDIte, Function.comp_apply]
      congr 1; apply Fin.ext; simp [fL_val]; omega
  right_inv p := by
    obtain ⟨p, q⟩ := p
    ext i
    · simp [eL_val, i.isLt]
    · simp [fL_val]

theorem splitQ_apply (h : N + m = N') (z : Qubits N') : splitQ h z = (z ∘ eL h, z ∘ fL h) := rfl

theorem eq_iff_split (h : N + m = N') (y z : Qubits N') :
    y = z ↔ y ∘ eL h = z ∘ eL h ∧ y ∘ fL h = z ∘ fL h := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply (splitQ h).injective
    rw [splitQ_apply, splitQ_apply, h1, h2]

theorem offRange_iff (h : N + m = N') (y z : Qubits N') :
    (∀ a : Fin N', a ∉ Set.range (eL h) → y a = z a) ↔ y ∘ fL h = z ∘ fL h := by
  constructor
  · intro H; funext j
    apply H
    rintro ⟨i, hi⟩; exact eL_ne_fL h i j hi
  · intro H a ha
    have hN : ¬ a.val < N := fun hlt => ha ⟨⟨a.val, hlt⟩, Fin.ext rfl⟩
    have := congrFun H ⟨a.val - N, by omega⟩
    simp only [Function.comp_apply] at this
    have e : fL h ⟨a.val - N, by omega⟩ = a := by apply Fin.ext; simp [fL_val]; omega
    rwa [e] at this

/-- `ρ ⊗ σ`, `ρ` on the old wires and `σ` on the fresh ones. -/
def tens (h : N + m = N') (ρ : Matrix (Qubits N) (Qubits N) ℂ) (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    Matrix (Qubits N') (Qubits N') ℂ :=
  Matrix.of fun y z => ρ (y ∘ eL h) (z ∘ eL h) * σ (y ∘ fL h) (z ∘ fL h)

theorem sum_split {M : Type*} [AddCommMonoid M] (h : N + m = N') (F : Qubits N' → M) :
    ∑ z, F z = ∑ p : Qubits N, ∑ q : Qubits m, F ((splitQ h).symm (p, q)) := by
  rw [← Fintype.sum_prod_type', ← (splitQ h).symm.sum_comp]

theorem split_symm_e (h : N + m = N') (p : Qubits N) (q : Qubits m) :
    (splitQ h).symm (p, q) ∘ eL h = p := by
  exact congrArg Prod.fst ((splitQ h).apply_symm_apply (p, q))

theorem split_symm_f (h : N + m = N') (p : Qubits N) (q : Qubits m) :
    (splitQ h).symm (p, q) ∘ fL h = q := by
  exact congrArg Prod.snd ((splitQ h).apply_symm_apply (p, q))

theorem embedOp_mul_tens (h : N + m = N') (A ρ : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    embedOp A (eL h) * tens h ρ σ = tens h (A * ρ) σ := by
  ext y z
  rw [Matrix.mul_apply, sum_split h]
  simp only [embedOp, tens, Matrix.of_apply, offRange_iff, split_symm_e, split_symm_f,
    Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_eq_single (y ∘ fL h)]
  · simp only [if_true]; ring
  · intro q _ hq; rw [if_neg (Ne.symm hq)]; ring
  · simp

theorem tens_mul_embedOp (h : N + m = N') (ρ B : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    tens h ρ σ * embedOp B (eL h) = tens h (ρ * B) σ := by
  ext y z
  rw [Matrix.mul_apply, sum_split h]
  simp only [embedOp, tens, Matrix.of_apply, offRange_iff, split_symm_e, split_symm_f,
    Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_eq_single (z ∘ fL h)]
  · simp only [if_true]; ring
  · intro q _ hq; rw [if_neg hq]; ring
  · simp

theorem trace_tens (h : N + m = N') (ρ : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    (tens h ρ σ).trace = ρ.trace * σ.trace := by
  simp only [Matrix.trace, Matrix.diag, tens, Matrix.of_apply]
  rw [sum_split h, Finset.sum_mul_sum]
  simp only [split_symm_e, split_symm_f]

/-- A gate application moved to the enlarged register. -/
def liftGA (h : N + m = N') (g : GateApp allSmallGates N) : GateApp allSmallGates N' :=
  ⟨g.gate, g.mem, g.wires.trans (eL h)⟩

/-- A circuit moved to the enlarged register. -/
def liftCirc (h : N + m = N') (c : QCircuit N) : QCircuit N' := c.map (liftGA h)

theorem liftCirc_unitary (h : N + m = N') (c : QCircuit N) :
    (liftCirc h c).unitary = embedOp c.unitary (eL h) := by
  induction c with
  | nil => simp [liftCirc, circuit_unitary_nil, embedOp_one]
  | cons g c ih =>
    have : liftCirc h (g :: c) = liftGA h g :: liftCirc h c := rfl
    rw [this, circuit_unitary_cons, circuit_unitary_cons, ih, embedOp_mul, embedOp_trans]
    rfl

theorem flipMask_map_e (h : N + m = N') (w : List (Fin N)) (x : Bits) (i : Fin N) :
    flipMask (w.map (eL h)) x (eL h i) = flipMask w x i := by
  simp only [flipMask, List.zip_map_left, List.any_map]
  congr 1; funext p
  simp [(eL h).injective.eq_iff]

theorem flipMask_map_off (h : N + m = N') (w : List (Fin N)) (x : Bits) (a : Fin N')
    (ha : a ∉ Set.range (eL h)) : flipMask (w.map (eL h)) x a = false := by
  simp only [flipMask, List.zip_map_left, List.any_map, List.any_eq_false]
  intro p _
  have : eL h p.1 ≠ a := fun hh => ha ⟨p.1, hh⟩
  simp [this]

theorem loadX_map (h : N + m = N') (w : List (Fin N)) (x : Bits) :
    loadX (w.map (eL h)) x = embedOp (loadX w x) (eL h) := by
  ext y z
  simp only [loadX, embedOp, Matrix.of_apply]
  have key : (y = fun a => xor (z a) (flipMask (w.map (eL h)) x a)) ↔
      ((∀ a : Fin N', a ∉ Set.range (eL h) → y a = z a) ∧
        (y ∘ eL h = fun a => xor ((z ∘ eL h) a) (flipMask w x a))) := by
    constructor
    · intro hy
      refine ⟨fun a ha => ?_, ?_⟩
      · rw [hy]; simp [flipMask_map_off h w x a ha]
      · funext i; rw [hy]; simp [flipMask_map_e]
    · rintro ⟨h1, h2⟩
      funext a
      by_cases ha : a ∈ Set.range (eL h)
      · obtain ⟨i, rfl⟩ := ha
        have := congrFun h2 i
        simp only [Function.comp_apply] at this
        rw [this, flipMask_map_e]
      · rw [h1 a ha, flipMask_map_off h w x a ha]; simp
  by_cases H : y = fun a => xor (z a) (flipMask (w.map (eL h)) x a)
  · rw [if_pos H, if_pos (key.1 H).1, if_pos (key.1 H).2]
  · rw [if_neg H]
    by_cases H1 : ∀ a : Fin N', a ∉ Set.range (eL h) → y a = z a
    · rw [if_pos H1, if_neg (fun H2 => H (key.2 ⟨H1, H2⟩))]
    · rw [if_neg H1]

theorem outcomeProj_map (h : N + m = N') (w : List (Fin N)) (c : Bits) :
    outcomeProj (w.map (eL h)) c = embedOp (outcomeProj w c) (eL h) := by
  ext y z
  simp only [outcomeProj, diagProj, embedOp, Matrix.of_apply, Matrix.diagonal_apply, readWires,
    List.map_map, offRange_iff]
  by_cases hyz : y = z
  · subst hyz; simp only [if_true]; split_ifs <;> simp_all
  · rw [if_neg hyz]
    rw [eq_iff_split h] at hyz
    by_cases h2 : y ∘ fL h = z ∘ fL h
    · rw [if_pos h2, if_neg (fun h1 => hyz ⟨h1, h2⟩)]
    · rw [if_neg h2]

theorem loadX_nil' {N : ℕ} (w : List (Fin N)) : loadX w [] = 1 := by
  ext y z
  simp [loadX, flipMask, Matrix.one_apply]

/-- A step moved to the enlarged register. -/
def liftStep (h : N + m = N') (s : RoundStep N) : RoundStep N' :=
  ⟨s.inW.map (eL h), liftCirc h s.circ, s.outW.map (eL h)⟩

theorem liftStep_op (h : N + m = N') (s : RoundStep N) (x : Bits) :
    (liftStep h s).op x = embedOp (s.op x) (eL h) := by
  simp only [RoundStep.op, liftStep, liftCirc_unitary, loadX_map, embedOp_mul]

theorem stepDM_lift (h : N + m = N') (s : RoundStep N) (x o : Bits)
    (ρ : Matrix (Qubits N) (Qubits N) ℂ) (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    stepDM (liftStep h s) x o (tens h ρ σ) = tens h (stepDM s x o ρ) σ := by
  simp only [stepDM, liftStep_op, embedOp_conjTranspose]
  have hP : outcomeProj (liftStep h s).outW o = embedOp (outcomeProj s.outW o) (eL h) :=
    outcomeProj_map h s.outW o
  rw [hP, ← embedOp_mul, embedOp_mul_tens, tens_mul_embedOp, tens_mul_embedOp]

end Lift
/-! ### CNOT copies of measured wires onto fresh ancillas -/

section Copy
variable {N N' : ℕ}

def cnotFun {n : ℕ} (a t : Fin n) (x : Qubits n) : Qubits n :=
  fun k => if k = t then xor (x t) (x a) else x k

theorem cnot_mat_eq :
    ((Gate.ofMatrix2 cnot).mat : Matrix (Qubits 2) (Qubits 2) ℂ) = permOf (N := 2) (cnotFun 0 1) := by
  show cnot.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b => (b 0, b 1)) = permOf (cnotFun 0 1)
  ext y z
  simp only [cnot, permOf, Matrix.submatrix_apply, Matrix.of_apply]
  have key : (y 0 = z 0 ∧ y 1 = xor (z 1) (z 0)) ↔ y = cnotFun 0 1 z := by
    constructor
    · rintro ⟨h0, h1⟩; funext k; fin_cases k <;> simp [cnotFun, h0, h1]
    · intro hh; rw [hh]; simp [cnotFun]
  by_cases H : y = cnotFun 0 1 z
  · rw [if_pos H, if_pos (key.2 H)]
  · rw [if_neg H, if_neg (fun hh => H (key.1 hh))]

theorem cnotFun_invol {n : ℕ} (a t : Fin n) (hat : a ≠ t) (x : Qubits n) :
    cnotFun a t (cnotFun a t x) = x := by
  funext k
  by_cases hkt : k = t
  · subst hkt; simp [cnotFun, hat]
  · simp [cnotFun, hkt]

theorem cnot_mem : Gate.ofMatrix2 cnot ∈ allSmallGates := by
  refine ⟨le_refl _, ?_⟩
  show (Gate.ofMatrix2 cnot).mat ∈ _
  rw [cnot_mat_eq]
  exact permOf_unitary (N := 2) _ (cnotFun_invol (0 : Fin 2) 1 (by decide))

def cnotWires {n : ℕ} (a t : Fin n) (hat : a ≠ t) : Fin 2 ↪ Fin n :=
  ⟨![a, t], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hat
    · exact absurd hij.symm hat
    · rfl⟩

def cnotGA {n : ℕ} (a t : Fin n) (hat : a ≠ t) : GateApp allSmallGates n :=
  ⟨Gate.ofMatrix2 cnot, cnot_mem, cnotWires a t hat⟩

theorem embedOp_cnot2 {n : ℕ} (a t : Fin n) (hat : a ≠ t) :
    embedOp (permOf (N := 2) (cnotFun 0 1)) (cnotWires a t hat) = permOf (cnotFun a t) := by
  ext y z
  simp only [embedOp, permOf, Matrix.of_apply]
  have hw0 : cnotWires a t hat 0 = a := rfl
  have hw1 : cnotWires a t hat 1 = t := rfl
  have hc : ((∀ k : Fin n, k ∉ Set.range (cnotWires a t hat) → y k = z k) ∧
      (y ∘ cnotWires a t hat = cnotFun 0 1 (z ∘ cnotWires a t hat))) ↔ y = cnotFun a t z := by
    constructor
    · rintro ⟨hk, h2⟩
      have ha := congrFun h2 0
      have ht := congrFun h2 1
      simp only [Function.comp_apply, cnotFun, hw0, hw1] at ha ht
      simp at ha ht
      funext k
      by_cases hkt : k = t
      · subst hkt; simp [cnotFun, ht]
      · by_cases hka : k = a
        · subst hka; simp [cnotFun, hat, ha]
        · have hnot : k ∉ Set.range (cnotWires a t hat) := by
            rintro ⟨i, hi⟩
            fin_cases i
            · exact hka hi.symm
            · exact hkt hi.symm
          simp [cnotFun, hkt, hk k hnot]
    · intro hz
      subst hz
      refine ⟨?_, ?_⟩
      · intro k hk
        have hkt : k ≠ t := fun hh => hk ⟨1, by rw [hw1, hh]⟩
        simp [cnotFun, hkt]
      · funext i
        fin_cases i
        · simp [cnotFun, hw0, hw1, hat]
        · simp [cnotFun, hw0, hw1]
  by_cases H : y = cnotFun a t z
  · rw [if_pos (hc.2 H).1, if_pos (hc.2 H).2, if_pos H]
  · rw [if_neg H]
    by_cases H1 : ∀ k : Fin n, k ∉ Set.range (cnotWires a t hat) → y k = z k
    · rw [if_pos H1, if_neg (fun H2 => H (hc.1 ⟨H1, H2⟩))]
    · rw [if_neg H1]

theorem embedOp_cnotGA {n : ℕ} (a t : Fin n) (hat : a ≠ t) :
    embedOp (cnotGA a t hat).gate.mat (cnotGA a t hat).wires = permOf (cnotFun a t) :=
  (congrArg (fun M : Matrix (Qubits 2) (Qubits 2) ℂ => embedOp M (cnotWires a t hat)) cnot_mat_eq).trans
    (embedOp_cnot2 a t hat)


/-- The CNOT from old wire `dW[j]` to fresh wire `j`. -/
def copyGA {dW : List (Fin N)} (h : N + dW.length = N') (j : Fin dW.length) :
    GateApp allSmallGates N' :=
  cnotGA (eL h (dW.get j)) (fL h j) (eL_ne_fL h _ _)

def copyFun {dW : List (Fin N)} (h : N + dW.length = N') :
    List (Fin dW.length) → Qubits N' → Qubits N'
  | [] => id
  | j :: l => copyFun h l ∘ cnotFun (eL h (dW.get j)) (fL h j)

theorem copy_unitary {dW : List (Fin N)} (h : N + dW.length = N') (l : List (Fin dW.length)) :
    Circuit.unitary (l.map (copyGA h)) = permOf (copyFun h l) := by
  induction l with
  | nil => simp [circuit_unitary_nil, copyFun, permOf_id]
  | cons j l ih =>
    rw [List.map_cons, circuit_unitary_cons, ih, copyGA, embedOp_cnotGA, permOf_mul]
    rfl

theorem copyFun_e {dW : List (Fin N)} (h : N + dW.length = N') (l : List (Fin dW.length))
    (z : Qubits N') (i : Fin N) : copyFun h l z (eL h i) = z (eL h i) := by
  induction l generalizing z with
  | nil => rfl
  | cons j l ih =>
    show copyFun h l (cnotFun _ _ z) (eL h i) = _
    rw [ih]
    simp [cnotFun, eL_ne_fL]

theorem copyFun_f {dW : List (Fin N)} (h : N + dW.length = N') (l : List (Fin dW.length))
    (hl : l.Nodup) (z : Qubits N') (j : Fin dW.length) :
    copyFun h l z (fL h j) =
      if j ∈ l then xor (z (fL h j)) (z (eL h (dW.get j))) else z (fL h j) := by
  induction l generalizing z with
  | nil => simp [copyFun]
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    show copyFun h l (cnotFun _ _ z) (fL h j) = _
    rw [ih hl.2]
    have hf : ∀ a b : Fin dW.length, fL h a = fL h b ↔ a = b := by
      intro a b; constructor
      · intro hh; have := congrArg Fin.val hh; simp [fL_val] at this; exact Fin.ext this
      · rintro rfl; rfl
    by_cases hjk : j = k
    · subst hjk
      simp [hl.1, cnotFun, eL_ne_fL]
    · have hjk' : fL h j ≠ fL h k := fun hh => hjk ((hf j k).1 hh)
      by_cases hjl : j ∈ l
      · simp [hjl, cnotFun, hjk', eL_ne_fL]
      · simp [hjl, hjk, cnotFun, hjk']

/-- The full copy circuit. -/
def copyCirc {dW : List (Fin N)} (h : N + dW.length = N') : QCircuit N' :=
  (List.finRange dW.length).map (copyGA h)

/-- What the copy circuit does on basis states. -/
def copyAll {dW : List (Fin N)} (h : N + dW.length = N') : Qubits N' → Qubits N' :=
  copyFun h (List.finRange dW.length)

theorem copyAll_e {dW : List (Fin N)} (h : N + dW.length = N') (z : Qubits N') :
    copyAll h z ∘ eL h = z ∘ eL h := funext fun i => copyFun_e h _ z i

theorem copyAll_f {dW : List (Fin N)} (h : N + dW.length = N') (z : Qubits N') :
    copyAll h z ∘ fL h = fun j => xor (z (fL h j)) (z (eL h (dW.get j))) := by
  funext j
  simp only [Function.comp_apply, copyAll]
  rw [copyFun_f h _ (List.nodup_finRange _)]
  simp

theorem copyAll_invol {dW : List (Fin N)} (h : N + dW.length = N') (z : Qubits N') :
    copyAll h (copyAll h z) = z := by
  rw [eq_iff_split h]
  refine ⟨by rw [copyAll_e, copyAll_e], ?_⟩
  rw [copyAll_f]
  funext j
  have h1 := congrFun (copyAll_f h z) j
  have h2 := congrFun (copyAll_e h z) (dW.get j)
  simp only [Function.comp_apply] at h1 h2
  show xor (copyAll h z (fL h j)) (copyAll h z (eL h (dW.get j))) = z (fL h j)
  rw [h1, h2]; simp

theorem copyCirc_unitary {dW : List (Fin N)} (h : N + dW.length = N') :
    (copyCirc h).unitary = permOf (copyAll h) := copy_unitary h _

theorem readWires_eq_ofFn_iff (dW : List (Fin N)) (p : Qubits N) (d : Qubits dW.length) :
    readWires dW p = List.ofFn d ↔ (fun j => p (dW.get j)) = d := by
  have : readWires dW p = List.ofFn (fun j => p (dW.get j)) := by
    simp only [readWires]
    conv_lhs => rw [← List.ofFn_get dW]
    rw [List.map_ofFn]; rfl
  rw [this, List.ofFn_inj]

theorem trace_diag_sandwich {n : ℕ} (a : Qubits n → ℂ) (X M : Matrix (Qubits n) (Qubits n) ℂ) :
    (Matrix.diagonal a * X * Matrix.diagonal a * M).trace =
      ∑ p, ∑ p', a p * X p p' * a p' * M p' p := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun p' _ => ?_))
  rw [Finset.sum_mul, Finset.sum_eq_single p']
  · simp [Matrix.diagonal_apply]
  · intro b _ hb; simp [Matrix.diagonal_apply, hb]
  · simp

/-- Deferred measurement: copying the wires `dW` onto fresh ancillas in `|0⟩` and tracing them out
equals measuring `dW` and summing over the outcomes. -/
theorem deferred_trace {dW : List (Fin N)} (h : N + dW.length = N')
    (X A B : Matrix (Qubits N) (Qubits N) ℂ) :
    (embedOp A (eL h) * ((copyCirc h).unitary * tens h X (zeroDM dW.length) * ((copyCirc h).unitary)ᴴ)
        * embedOp B (eL h)).trace =
      ∑ d : Qubits dW.length,
        (A * outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B).trace := by
  set r : Qubits N → Qubits dW.length := fun p j => p (dW.get j) with hr
  -- entries of the copied state
  have hT : ∀ y z, ((copyCirc h).unitary * tens h X (zeroDM dW.length) * ((copyCirc h).unitary)ᴴ) y z
      = X (y ∘ eL h) (z ∘ eL h) * (if y ∘ fL h = r (y ∘ eL h) then 1 else 0) *
        (if z ∘ fL h = r (z ∘ eL h) then 1 else 0) := by
    intro y z
    rw [copyCirc_unitary, permOf_conj_apply _ (copyAll_invol h)]
    simp only [tens, Matrix.of_apply, copyAll_e, zeroDM, copyAll_f]
    have e1 : ∀ w : Qubits N', ((fun j => xor (w (fL h j)) (w (eL h (dW.get j)))) = fun _ => false)
        ↔ w ∘ fL h = r (w ∘ eL h) := by
      intro w
      constructor
      · intro hh; funext j; have := congrFun hh j; simp only [Function.comp_apply, hr]
        simpa using this
      · intro hh; funext j; have := congrFun hh j; simp only [Function.comp_apply, hr] at this
        simp [this]
    by_cases hy : y ∘ fL h = r (y ∘ eL h)
    · by_cases hz : z ∘ fL h = r (z ∘ eL h)
      · rw [if_pos ⟨(e1 y).2 hy, (e1 z).2 hz⟩, if_pos hy, if_pos hz]; ring
      · rw [if_neg (fun hh => hz ((e1 z).1 hh.2)), if_neg hz]; ring
    · rw [if_neg (fun hh => hy ((e1 y).1 hh.1)), if_neg hy]; ring
  -- left side
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← embedOp_mul]
  have lhs : ∀ (T : Matrix (Qubits N') (Qubits N') ℂ) (M : Matrix (Qubits N) (Qubits N) ℂ),
      (T * embedOp M (eL h)).trace = ∑ y, ∑ z, T y z * embedOp M (eL h) z y := by
    intro T M; simp [Matrix.trace, Matrix.mul_apply]
  rw [lhs]
  simp_rw [hT]
  rw [sum_split h]
  simp_rw [sum_split h (fun z => _ * embedOp _ _ z _)]
  simp only [split_symm_e, split_symm_f, embedOp, Matrix.of_apply, offRange_iff]
  calc _ = ∑ p, ∑ p', X p p' * (B * A) p' p * (if r p' = r p then 1 else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p' _ => ?_)
        rw [Finset.sum_eq_single (r p)]
        · rw [Finset.sum_eq_single (r p')]
          · by_cases hpp : r p' = r p <;> simp [hpp]
          · intro q _ hq; simp [hq]
          · simp
        · intro q _ hq; simp [hq]
        · simp
    _ = _ := by
        have rhs : ∀ d : Qubits dW.length,
            (A * outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B).trace =
              ∑ p : Qubits N, ∑ p' : Qubits N, (if r p = d then (1 : ℂ) else 0) * X p p' *
                (if r p' = d then 1 else 0) * (B * A) p' p := by
          intro d
          have e : A * outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B =
              A * (outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B) := by
            simp only [Matrix.mul_assoc]
          rw [e, Matrix.trace_mul_comm]
          have e2 : outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B * A =
              outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * (B * A) := by
            simp only [Matrix.mul_assoc]
          rw [e2]
          simp only [outcomeProj, diagProj]
          rw [trace_diag_sandwich]
          simp only [readWires_eq_ofFn_iff]
          rfl
        simp_rw [rhs]
        symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p' _ => ?_)
        rw [Finset.sum_eq_single (r p)]
        · by_cases hpp : r p' = r p <;> simp [hpp]
        · intro d _ hd; simp [Ne.symm hd]
        · simp

end Copy

/-! ### Runs -/

theorem runFrom_append (S : QStrategy) (msg : List Bits → Bits) (l₁ l₂ done : List Bits)
    (ρ : Matrix (Qubits S.N) (Qubits S.N) ℂ) :
    S.runFrom msg done (l₁ ++ l₂) ρ = S.runFrom msg (done ++ l₁) l₂ (S.runFrom msg done l₁ ρ) := by
  induction l₁ generalizing done ρ with
  | nil => simp [QStrategy.runFrom]
  | cons o l ih =>
    simp only [List.cons_append, QStrategy.runFrom]
    rw [ih]; simp

theorem runFrom_lift {m : ℕ} (S S' : QStrategy) (h : S.N + m = S'.N) (K : ℕ)
    (hstep : ∀ j < K, S'.stepAt j = liftStep h (S.stepAt j)) (msg msg' : List Bits → Bits)
    (hmsg : ∀ d : List Bits, d.length < K → msg' d = msg d)
    (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    ∀ (os done : List Bits) (ρ : Matrix (Qubits S.N) (Qubits S.N) ℂ), done.length + os.length ≤ K →
      S'.runFrom msg' done os (tens h ρ σ) = tens h (S.runFrom msg done os ρ) σ := by
  intro os
  induction os with
  | nil => intro done ρ _; simp [QStrategy.runFrom]
  | cons o rest ih =>
    intro done ρ hl
    simp only [List.length_cons] at hl
    simp only [QStrategy.runFrom]
    rw [hstep _ (by omega), hmsg _ (by omega), stepDM_lift]
    exact ih _ _ (by simp; omega)

section PSD
open scoped ComplexOrder

theorem initDM_zero_psd (S : QStrategy) : (S.initDM (zeroDM S.inQ)).PosSemidef := by
  have : S.initDM (zeroDM S.inQ) = Matrix.vecMulVec
      (fun y => (if fstPart y = (fun _ => false) then 1 else 0) * S.advice (sndPart y))
      (star fun y => (if fstPart y = (fun _ => false) then 1 else 0) * S.advice (sndPart y)) := by
    ext y z
    simp only [QStrategy.initDM, zeroDM, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      star_mul']
    by_cases hy : fstPart y = (fun _ => false)
    · by_cases hz : fstPart z = (fun _ => false)
      · simp [hy, hz]
        try ring
      · simp [hy, hz]
    · simp [hy]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem outcomeProj_conjTranspose {N : ℕ} (w : List (Fin N)) (c : Bits) :
    (outcomeProj w c)ᴴ = outcomeProj w c := by
  simp only [outcomeProj, diagProj, Matrix.diagonal_conjTranspose]
  congr 1; funext z; simp only [Pi.star_apply]; split_ifs <;> simp

theorem stepDM_psd {N : ℕ} (s : RoundStep N) (x o : Bits) {ρ : Matrix (Qubits N) (Qubits N) ℂ}
    (hρ : ρ.PosSemidef) : (stepDM s x o ρ).PosSemidef := by
  have : stepDM s x o ρ = (outcomeProj s.outW o * s.op x) * ρ * (outcomeProj s.outW o * s.op x)ᴴ := by
    simp only [stepDM, Matrix.conjTranspose_mul, outcomeProj_conjTranspose, Matrix.mul_assoc]
  rw [this]
  exact hρ.mul_mul_conjTranspose_same _

theorem runFrom_psd (S : QStrategy) (msg : List Bits → Bits) :
    ∀ (os done : List Bits) {ρ : Matrix (Qubits S.N) (Qubits S.N) ℂ}, ρ.PosSemidef →
      (S.runFrom msg done os ρ).PosSemidef := by
  intro os
  induction os with
  | nil => intro done ρ hρ; simpa [QStrategy.runFrom] using hρ
  | cons o rest ih =>
    intro done ρ hρ
    simp only [QStrategy.runFrom]
    exact ih _ (stepDM_psd _ _ _ hρ)

theorem run_trace_nonneg (S : QStrategy) (msg : List Bits → Bits) (os : List Bits) :
    0 ≤ (S.run msg (zeroDM S.inQ) os).trace.re := by
  have := (runFrom_psd S msg os [] (initDM_zero_psd S)).trace_nonneg
  exact (Complex.nonneg_iff.1 this).1

end PSD


/-! ## Sums over measurement outcomes as sums over strings of given lengths -/

/-- `∑` over lists of strings with prescribed lengths. -/
noncomputable def lensSum : List ℕ → (List Bits → ℝ) → ℝ
  | [], F => F []
  | a :: l, F => ∑ x : Qubits a, lensSum l (fun t => F (List.ofFn x :: t))

theorem sum_outs_eq (r : ℕ) : ∀ (g : ℕ → ℕ) (F : List Bits → ℝ),
    ∑ o : ((j : Fin r) → Qubits (g j)), F (List.ofFn fun j => List.ofFn (o j)) =
      lensSum ((List.range r).map g) F := by
  induction r with
  | zero => intro g F; simp [lensSum]
  | succ r ih =>
    intro g F
    rw [← (Fin.consEquiv (fun j : Fin (r + 1) => Qubits (g j))).sum_comp, Fintype.sum_prod_type]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [lensSum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have := ih (fun k => g (k + 1)) (fun t => F (List.ofFn x :: t))
    simp only [List.ofFn_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    convert this using 2
    all_goals rfl

theorem sum_outs_eq' (S : QStrategy) (r : ℕ) (F : List Bits → ℝ) :
    ∑ o : S.Outs r, F (QStrategy.outList o) =
      lensSum ((List.range r).map fun j => (S.stepAt j).outW.length) F :=
  sum_outs_eq r (fun j => (S.stepAt j).outW.length) F

theorem lensSum_append (l₁ l₂ : List ℕ) : ∀ F : List Bits → ℝ,
    lensSum (l₁ ++ l₂) F = lensSum l₁ (fun p => lensSum l₂ (fun q => F (p ++ q))) := by
  induction l₁ with
  | nil => intro F; simp [lensSum]
  | cons a l ih => intro F; simp only [List.cons_append, lensSum, ih]

theorem lensSum_mono (l : List ℕ) : ∀ F G : List Bits → ℝ,
    (∀ p : List Bits, p.length = l.length → F p ≤ G p) → lensSum l F ≤ lensSum l G := by
  induction l with
  | nil => intro F G h; exact h [] rfl
  | cons a l ih =>
    intro F G h
    simp only [lensSum]
    refine Finset.sum_le_sum (fun x _ => ih _ _ (fun p hp => h _ (by simp [hp])))

theorem lensSum_add (l : List ℕ) : ∀ F G : List Bits → ℝ,
    lensSum l (fun p => F p + G p) = lensSum l F + lensSum l G := by
  induction l with
  | nil => intro F G; rfl
  | cons a l ih =>
    intro F G
    simp only [lensSum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => ih _ _)

theorem lensSum_congr (l : List ℕ) : ∀ F G : List Bits → ℝ,
    (∀ p : List Bits, p.length = l.length → F p = G p) → lensSum l F = lensSum l G := by
  intro F G h
  exact le_antisymm (lensSum_mono l F G (fun p hp => (h p hp).le))
    (lensSum_mono l G F (fun p hp => (h p hp).ge))

theorem lensSum_single (a : ℕ) (F : List Bits → ℝ) :
    lensSum [a] F = ∑ x : Qubits a, F [List.ofFn x] := rfl

/-! ## Structure of packed strings -/

theorem packOne_nil : packOne [] = [false] := rfl

theorem packOne_cons (b : Bool) (u : Bits) : packOne (b :: u) = true :: b :: packOne u := by
  simp [packOne]

theorem packOne_length (u : Bits) : (packOne u).length = 2 * u.length + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih => rw [packOne_cons]; simp [ih]; ring

theorem unpackAux_cons_spec : ∀ (s cur u : Bits) (rest : List Bits), unpackAux s cur = u :: rest →
    ∃ v s', u = cur.reverse ++ v ∧ s = packOne v ++ s' ∧ unpackAux s' [] = rest := by
  intro s cur
  induction s, cur using unpackAux.induct with
  | case1 cur => intro u rest h; simp [unpackAux] at h
  | case2 rest' cur =>
    intro u rest h
    simp only [unpackAux, List.cons.injEq] at h
    exact ⟨[], rest', by simp [h.1], by simp [packOne_nil], h.2⟩
  | case3 b rest' cur ih =>
    intro u rest h
    simp only [unpackAux] at h
    obtain ⟨v, s', hu, hs, hr⟩ := ih u rest h
    refine ⟨b :: v, s', by simp [hu], by rw [hs, packOne_cons]; rfl, hr⟩
  | case4 cur => intro u rest h; simp [unpackAux] at h

theorem pack_two_ne_nil (x y : Bits) : pack [x, y] ≠ [] := by
  simp [pack, packOne]

/-- If the first two items of `unpack s` are nonempty, `s` begins with their encodings. -/
theorem unpack_two_prefix (s u0 u1 : Bits) (h0 : (unpack s).getD 0 [] = u0)
    (h1 : (unpack s).getD 1 [] = u1) (hu0 : u0 ≠ []) (hu1 : u1 ≠ []) :
    ∃ t, s = packOne u0 ++ packOne u1 ++ t := by
  unfold unpack at h0 h1
  rcases hs : unpackAux s [] with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rw [hs] at h0; simp at h0; exact absurd h0 hu0
  · rw [hs] at h1; simp at h1; exact absurd h1 hu1
  · rw [hs] at h0 h1
    simp at h0 h1
    subst h0; subst h1
    obtain ⟨v, s', hv, hs', hr⟩ := unpackAux_cons_spec s [] a (b :: rest) hs
    obtain ⟨v', t, hv', ht, _⟩ := unpackAux_cons_spec s' [] b rest hr
    simp at hv hv'
    subst hv; subst hv'
    exact ⟨t, by rw [hs', ht, List.append_assoc]⟩

theorem unpackAux_packOne (x rest cur : Bits) :
    unpackAux (packOne x ++ rest) cur = (cur.reverse ++ x) :: unpackAux rest [] := by
  induction x generalizing cur with
  | nil => simp [packOne, unpackAux]
  | cons b x ih =>
    have : packOne (b :: x) ++ rest = true :: b :: (packOne x ++ rest) := by simp [packOne]
    rw [this, unpackAux, ih]; simp

theorem unpack_pack (l : List Bits) : unpack (pack l) = l := by
  induction l with
  | nil => simp [pack, unpack, unpackAux]
  | cons a l ih =>
    unfold unpack at ih ⊢
    have : pack (a :: l) = packOne a ++ pack l := by simp [pack]
    rw [this, unpackAux_packOne, ih]; simp

theorem op_nil {N : ℕ} (s : RoundStep N) : s.op [] = s.circ.unitary := by
  simp [RoundStep.op, loadX_nil']

/-! ## From the lemma_5 development -/
/-! ## Unitarity of steps (embedOp lemmas adapted from accepted QAlgorithms solutions) -/

noncomputable def wireEquivL {k n : ℕ} (w : Fin k ↪ Fin n) :
    Fin n ≃ Fin k ⊕ {a : Fin n // a ∉ Set.range w} :=
  (Equiv.sumCompl (fun a => a ∈ Set.range w)).symm.trans
    (((Equiv.ofInjective w w.injective).symm).sumCongr (Equiv.refl _))

noncomputable def qubitsSplitEquivL {k n : ℕ} (w : Fin k ↪ Fin n) :
    Qubits n ≃ Qubits k × ({a : Fin n // a ∉ Set.range w} → Bool) :=
  (Equiv.arrowCongr (wireEquivL w) (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

lemma qubitsSplitEquivL_comp_w {k n : ℕ} (w : Fin k ↪ Fin n)
    (u : Qubits k) (v : {a : Fin n // a ∉ Set.range w} → Bool) :
    (qubitsSplitEquivL w).symm (u, v) ∘ w = u := by
  ext i
  simp [qubitsSplitEquivL, wireEquivL]

lemma qubitsSplitEquivL_apply_not_range {k n : ℕ} (w : Fin k ↪ Fin n)
    (u : Qubits k) (v : {a : Fin n // a ∉ Set.range w} → Bool)
    (a : Fin n) (ha : a ∉ Set.range w) :
    (qubitsSplitEquivL w).symm (u, v) a = v ⟨a, ha⟩ := by
  simp [qubitsSplitEquivL, wireEquivL, ha]

lemma embedOp_one_L {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz
    simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso
      apply hyz
      ext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨i, rfl⟩ := ha
        exact congr_fun h2 i
      · exact h1 a ha
    · rfl
    · rfl

lemma conjTranspose_embedOp_L {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    (embedOp M w)ᴴ = embedOp Mᴴ w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.conjTranspose_apply]
  split_ifs with h1 h2 h3
  · rfl
  · exfalso; apply h2; intro a ha; rw [eq_comm]; exact h1 a ha
  · exfalso; apply h1; intro a ha; rw [eq_comm]; exact h3 a ha
  · simp

lemma embedOp_mul_L {k n : ℕ} (M N : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp M w * embedOp N w = embedOp (M * N) w := by
  ext y z
  simp only [embedOp, Matrix.mul_apply, Matrix.of_apply]
  by_cases hyz : ∀ a ∉ Set.range w, y a = z a
  · rw [if_pos hyz]
    rw [← (qubitsSplitEquivL w).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp_rw [qubitsSplitEquivL_comp_w]
    have h_inner : ∀ u : Qubits k,
        (∑ v : {a // a ∉ Set.range w} → Bool,
          (if ∀ a ∉ Set.range w, y a = (qubitsSplitEquivL w).symm (u, v) a then M (y ∘ w) u else 0) *
          (if ∀ a ∉ Set.range w, (qubitsSplitEquivL w).symm (u, v) a = z a then N u (z ∘ w) else 0)) =
        M (y ∘ w) u * N u (z ∘ w) := by
      intro u
      let v₀ : {a // a ∉ Set.range w} → Bool := fun ⟨a, _⟩ => y a
      have hv₀_y : ∀ a (ha : a ∉ Set.range w), y a = (qubitsSplitEquivL w).symm (u, v₀) a :=
        fun a ha => by rw [qubitsSplitEquivL_apply_not_range w u v₀ a ha]
      have hv₀_z : ∀ a (ha : a ∉ Set.range w), (qubitsSplitEquivL w).symm (u, v₀) a = z a :=
        fun a ha => by
          rw [qubitsSplitEquivL_apply_not_range w u v₀ a ha]
          exact hyz a ha
      rw [Fintype.sum_eq_single v₀]
      · rw [if_pos hv₀_y, if_pos hv₀_z]
      · intro v hv
        have : ∃ a ha, y a ≠ v ⟨a, ha⟩ := by
          by_contra hc
          apply hv
          ext ⟨a, ha⟩
          by_contra h_eq
          exact hc ⟨a, ha, Ne.symm h_eq⟩
        rcases this with ⟨a, ha, hne⟩
        have h_cond : ¬ (∀ b ∉ Set.range w, y b = (qubitsSplitEquivL w).symm (u, v) b) := by
          intro hall
          have := hall a ha
          rw [qubitsSplitEquivL_apply_not_range w u v a ha] at this
          exact hne this
        rw [if_neg h_cond, MulZeroClass.zero_mul]
    simp_rw [h_inner]
  · rw [if_neg hyz]
    have : ∃ a, a ∉ Set.range w ∧ y a ≠ z a := by
      by_contra hc
      apply hyz
      intro a ha
      by_contra hne
      exact hc ⟨a, ha, hne⟩
    rcases this with ⟨a, ha, hne⟩
    apply Finset.sum_eq_zero
    intro j _
    by_cases h1 : ∀ b ∉ Set.range w, y b = j b
    · by_cases h2 : ∀ b ∉ Set.range w, j b = z b
      · exact absurd ((h1 a ha).trans (h2 a ha)) hne
      · rw [if_neg h2, MulZeroClass.mul_zero]
    · rw [if_neg h1, MulZeroClass.zero_mul]

lemma embedOp_mem_unitaryGroup_L {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin n) (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, conjTranspose_embedOp_L, embedOp_mul_L]
  have : Mᴴ * M = (1 : Matrix (Qubits k) (Qubits k) ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hM
  rw [this, embedOp_one_L]

lemma qcircuit_unitary_mem {N : ℕ} (c : QCircuit N) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits N) ℂ := by
  dsimp [Circuit.unitary]
  apply Submonoid.list_prod_mem
  intro x hx
  rw [List.mem_reverse, List.mem_map] at hx
  rcases hx with ⟨g, _, rfl⟩
  exact embedOp_mem_unitaryGroup_L g.gate.mat g.wires g.mem.2

lemma loadX_mem {N : ℕ} (w : List (Fin N)) (x : Bits) :
    loadX w x ∈ Matrix.unitaryGroup (Qubits N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext y z
  simp only [loadX, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  have hinj : ∀ a b : Qubits N, ((fun i => xor (a i) (flipMask w x i)) =
      (fun i => xor (b i) (flipMask w x i))) ↔ a = b := by
    intro a b
    constructor
    · intro h; funext i; have := congr_fun h i; simpa using this
    · intro h; rw [h]
  rw [Finset.sum_eq_single (fun i => xor (y i) (flipMask w x i))]
  · by_cases h : y = z
    · subst h; simp
    · simp only [if_true, star_one, one_mul]
      rw [if_neg (fun h' => h ((hinj y z).1 h')), if_neg h]
  · intro b _ hb
    rw [if_neg hb]; simp
  · simp

lemma op_unitary {N : ℕ} (s : RoundStep N) (x : Bits) : (s.op x)ᴴ * s.op x = 1 := by
  have h : s.op x ∈ Matrix.unitaryGroup (Qubits N) ℂ :=
    Submonoid.mul_mem _ (qcircuit_unitary_mem s.circ) (loadX_mem s.inW x)
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp h

lemma op_unitary' {N : ℕ} (s : RoundStep N) (x : Bits) : s.op x * (s.op x)ᴴ = 1 := by
  have h : s.op x ∈ Matrix.unitaryGroup (Qubits N) ℂ :=
    Submonoid.mul_mem _ (qcircuit_unitary_mem s.circ) (loadX_mem s.inW x)
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp h

/-! ## Outcome projectors -/
lemma ofFn_readWires {N : ℕ} (w : List (Fin N)) (z : Qubits N) :
    List.ofFn (fun i : Fin w.length => z (w.get i)) = readWires w z := by
  apply List.ext_get
  · simp [readWires]
  · intro i h1 h2; simp [readWires]

lemma sum_ofFn_ite {N : ℕ} {M : Type*} [AddCommMonoid M] (w : List (Fin N)) (z : Qubits N)
    (F : Qubits w.length → M) :
    (∑ x : Qubits w.length, if readWires w z = List.ofFn x then F x else 0) =
      F (fun i => z (w.get i)) := by
  rw [Finset.sum_eq_single (fun i => z (w.get i))]
  · rw [if_pos (ofFn_readWires w z).symm]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    exact List.ofFn_injective (h.symm.trans (ofFn_readWires w z).symm)
  · simp

lemma outcomeProj_conjTranspose_L {N : ℕ} (w : List (Fin N)) (c : Bits) :
    (outcomeProj w c)ᴴ = outcomeProj w c := by
  simp only [outcomeProj, diagProj, Matrix.diagonal_conjTranspose]
  congr 1; funext z; simp only [Pi.star_apply]; split_ifs <;> simp

lemma outcomeProj_idem {N : ℕ} (w : List (Fin N)) (c : Bits) :
    outcomeProj w c * outcomeProj w c = outcomeProj w c := by
  simp only [outcomeProj, diagProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext z; split_ifs <;> simp

lemma sum_outcomeProj {N : ℕ} (w : List (Fin N)) :
    (∑ x : Qubits w.length, outcomeProj w (List.ofFn x)) = 1 := by
  ext y z
  simp only [outcomeProj, diagProj, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : y = z
  · subst h; simp only [if_true]
    exact sum_ofFn_ite w y (fun _ => (1 : ℂ))
  · simp [h]

/-! ## Runs: append, purity, total trace -/

lemma runFrom_snoc (S : QStrategy) (msg : List Bits → Bits) (l : List Bits) :
    ∀ (done : List Bits) (x : Bits) (ρ : Matrix (Qubits S.N) (Qubits S.N) ℂ),
    S.runFrom msg done (l ++ [x]) ρ =
      stepDM (S.stepAt (done ++ l).length) (msg (done ++ l)) x (S.runFrom msg done l ρ) := by
  induction l with
  | nil => intro done x ρ; simp [QStrategy.runFrom]
  | cons a l ih =>
    intro done x ρ
    simp only [List.cons_append, QStrategy.runFrom]
    rw [ih]
    simp

lemma stepDM_pure {N : ℕ} (s : RoundStep N) (m o : Bits) (B : Matrix (Qubits N) Unit ℂ) :
    stepDM s m o (B * Bᴴ) =
      (outcomeProj s.outW o * s.op m * B) * (outcomeProj s.outW o * s.op m * B)ᴴ := by
  simp only [stepDM, Matrix.conjTranspose_mul, outcomeProj_conjTranspose, Matrix.mul_assoc]

lemma runFrom_pure (S : QStrategy) (msg : List Bits → Bits) (os : List Bits) :
    ∀ (done : List Bits) (B : Matrix (Qubits S.N) Unit ℂ),
    ∃ B' : Matrix (Qubits S.N) Unit ℂ, S.runFrom msg done os (B * Bᴴ) = B' * B'ᴴ := by
  induction os with
  | nil => intro done B; exact ⟨B, rfl⟩
  | cons a l ih =>
    intro done B
    simp only [QStrategy.runFrom]
    rw [stepDM_pure]
    exact ih _ _

lemma initDM_zero_pure (S : QStrategy) :
    ∃ B : Matrix (Qubits S.N) Unit ℂ, S.initDM (zeroDM S.inQ) = B * Bᴴ := by
  refine ⟨Matrix.of fun y _ => (if fstPart y = (fun _ => false) then 1 else 0) *
    S.advice (sndPart y), ?_⟩
  ext y z
  simp only [QStrategy.initDM, zeroDM, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.univ_unique, Finset.sum_singleton, star_mul']
  by_cases hy : fstPart y = (fun _ => false) <;> by_cases hz : fstPart z = (fun _ => false) <;>
    simp [hy, hz]

lemma run_pure (S : QStrategy) (msg : List Bits → Bits) (os : List Bits) :
    ∃ B : Matrix (Qubits S.N) Unit ℂ, S.run msg (zeroDM S.inQ) os = B * Bᴴ := by
  obtain ⟨B, hB⟩ := initDM_zero_pure S
  unfold QStrategy.run
  rw [hB]
  exact runFrom_pure S msg os [] B

lemma sum_stepDM_trace {N : ℕ} (s : RoundStep N) (m : Bits) (ρ : Matrix (Qubits N) (Qubits N) ℂ) :
    (∑ x : Qubits s.outW.length, (stepDM s m (List.ofFn x) ρ).trace) = ρ.trace := by
  have h1 : ∀ x : Qubits s.outW.length, (stepDM s m (List.ofFn x) ρ).trace =
      (outcomeProj s.outW (List.ofFn x) * (s.op m * ρ * (s.op m)ᴴ)).trace := by
    intro x
    simp only [stepDM]
    rw [Matrix.trace_mul_comm]
    rw [show outcomeProj s.outW (List.ofFn x) *
        (outcomeProj s.outW (List.ofFn x) * s.op m * ρ * (s.op m)ᴴ) =
        (outcomeProj s.outW (List.ofFn x) * outcomeProj s.outW (List.ofFn x)) *
          (s.op m * ρ * (s.op m)ᴴ) by simp only [Matrix.mul_assoc], outcomeProj_idem]
  simp_rw [h1]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, sum_outcomeProj, Matrix.one_mul,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, op_unitary, Matrix.one_mul]

lemma outList_snoc (S : QStrategy) (K : ℕ) (o : S.Outs K)
    (x : Qubits (S.stepAt K).outW.length) :
    QStrategy.outList (S := S) (K := K + 1)
      (Fin.snoc (α := fun j : Fin (K + 1) => Qubits (S.stepAt j).outW.length) o x) =
      QStrategy.outList o ++ [List.ofFn x] := by
  simp only [QStrategy.outList]
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 2
  · funext i
    simp [Fin.snoc_castSucc]
  · simp [Fin.snoc_last]

lemma sum_outs_succ {M : Type*} [AddCommMonoid M] (S : QStrategy) (K : ℕ) (f : List Bits → M) :
    (∑ o : S.Outs (K + 1), f (QStrategy.outList o)) =
      ∑ o : S.Outs K, ∑ x : Qubits (S.stepAt K).outW.length,
        f (QStrategy.outList o ++ [List.ofFn x]) := by
  rw [← (Fin.snocEquiv (fun j : Fin (K + 1) => Qubits (S.stepAt j).outW.length)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg f (outList_snoc S K o x)

lemma sum_run_trace (S : QStrategy) (msg : List Bits → Bits)
    (ρ0 : Matrix (Qubits S.inQ) (Qubits S.inQ) ℂ) (K : ℕ) :
    (∑ o : S.Outs K, (S.run msg ρ0 (QStrategy.outList o)).trace) = (S.initDM ρ0).trace := by
  induction K with
  | zero =>
    rw [Fintype.sum_unique]
    simp [QStrategy.outList, QStrategy.run, QStrategy.runFrom]
  | succ K ih =>
    rw [sum_outs_succ S K (fun l => (S.run msg ρ0 l).trace)]
    rw [← ih]
    apply Finset.sum_congr rfl
    intro o _
    simp only [QStrategy.run]
    simp_rw [runFrom_snoc]
    have hl : ([] ++ QStrategy.outList o).length = K := by simp [QStrategy.outList]
    rw [hl]
    exact sum_stepDM_trace _ _ _

lemma initDM_zero_trace (S : QStrategy) (hS : S.Valid) :
    (S.initDM (zeroDM S.inQ)).trace = 1 := by
  let e : Qubits S.N ≃ Qubits S.inQ × Qubits S.wkQ :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  have he : ∀ y, e y = (fstPart y, sndPart y) := by
    intro y
    ext i <;> simp [e, fstPart, sndPart]
  let F : Qubits S.inQ → Qubits S.wkQ → ℂ := fun u v =>
    zeroDM S.inQ u u * S.advice v * star (S.advice v)
  have h1 : (S.initDM (zeroDM S.inQ)).trace = ∑ y, F (fstPart y) (sndPart y) := by
    simp [Matrix.trace, QStrategy.initDM, F]
  rw [h1]
  have h2 : (∑ y, F (fstPart y) (sndPart y)) = ∑ p : Qubits S.inQ × Qubits S.wkQ, F p.1 p.2 := by
    rw [← e.sum_comp (fun p => F p.1 p.2)]
    simp only [he]
  rw [h2, Fintype.sum_prod_type, Finset.sum_eq_single (fun _ => false)]
  · simp only [F, zeroDM, Matrix.of_apply, and_self, if_true, one_mul]
    have h3 : ∀ v, S.advice v * star (S.advice v) = ((‖S.advice v‖ ^ 2 : ℝ) : ℂ) := by
      intro v
      rw [Complex.star_def, Complex.mul_conj']
      push_cast; ring
    simp_rw [h3]
    rw [← Complex.ofReal_sum, hS.1]
    simp
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro v _
    simp [F, zeroDM, hu]
  · simp



lemma star_mul_self_eq_norm_sq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.star_def, Complex.mul_conj']
  push_cast; ring

lemma trace_unit_self {ι : Type*} [Fintype ι] (B : Matrix ι Unit ℂ) :
    (Bᴴ * B).trace = ((∑ i, ‖B i ()‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.univ_unique, Finset.sum_singleton, star_mul_self_eq_norm_sq]
  push_cast; rfl

lemma trace_unit_cs {ι : Type*} [Fintype ι] (B Y : Matrix ι Unit ℂ) :
    ‖(Bᴴ * Y).trace‖ ≤ √((Bᴴ * B).trace.re) * √((Yᴴ * Y).trace.re) := by
  rw [trace_unit_self, trace_unit_self, Complex.ofReal_re, Complex.ofReal_re]
  have ht : (Bᴴ * Y).trace = ∑ i, star (B i ()) * Y i () := by
    simp [Matrix.trace, Matrix.mul_apply]
  rw [ht]
  calc ‖∑ i, star (B i ()) * Y i ()‖ ≤ ∑ i, ‖star (B i ()) * Y i ()‖ := norm_sum_le _ _
    _ = ∑ i, ‖B i ()‖ * ‖Y i ()‖ := by simp
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

lemma trace_mul_self_re_nonneg {ι : Type*} [Fintype ι] (Y : Matrix ι Unit ℂ) :
    0 ≤ (Y * Yᴴ).trace.re := by
  rw [Matrix.trace_mul_comm, trace_unit_self, Complex.ofReal_re]
  positivity

/-- The branch inequality of the collapse experiment, in abstract form. -/
lemma sum_proj_sandwich {N : ℕ} (w : List (Fin N)) (X : Matrix (Qubits N) (Qubits N) ℂ) :
    (∑ m : Qubits w.length, outcomeProj w (List.ofFn m) * X * outcomeProj w (List.ofFn m)) =
      Matrix.of fun y z => if readWires w y = readWires w z then X y z else 0 := by
  ext y z
  rw [Matrix.sum_apply]
  have h : ∀ m : Qubits w.length,
      (outcomeProj w (List.ofFn m) * X * outcomeProj w (List.ofFn m)) y z =
      if readWires w y = List.ofFn m then
        X y z * (if readWires w z = List.ofFn m then 1 else 0) else 0 := by
    intro m
    simp only [outcomeProj, diagProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
    split_ifs <;> simp
  simp_rw [h]
  rw [sum_ofFn_ite w y (fun m => X y z * if readWires w z = List.ofFn m then 1 else 0)]
  simp only [ofFn_readWires, Matrix.of_apply]
  by_cases hyz : readWires w y = readWires w z
  · rw [if_pos hyz.symm, if_pos hyz, mul_one]
  · rw [if_neg (Ne.symm hyz), if_neg hyz, mul_zero]

/-- The adjoint circuit: gates reversed, each replaced by its conjugate transpose. -/
noncomputable def QCircuit.adj {N : ℕ} (c : QCircuit N) : QCircuit N :=
  (c.map fun g => (⟨⟨g.gate.arity, g.gate.matᴴ⟩,
    ⟨g.mem.1, by
      show g.gate.matᴴ ∈ Matrix.unitaryGroup _ ℂ
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem g.mem.2⟩, g.wires⟩ :
      GateApp allSmallGates N)).reverse

lemma QCircuit.adj_size {N : ℕ} (c : QCircuit N) : (QCircuit.adj c).size = c.size := by
  simp [QCircuit.adj, Circuit.size]

lemma QCircuit.adj_unitary {N : ℕ} (c : QCircuit N) :
    Circuit.unitary (QCircuit.adj c) = (Circuit.unitary c)ᴴ := by
  induction c with
  | nil => simp [QCircuit.adj, Circuit.unitary]
  | cons g l ih =>
    have h1 : QCircuit.adj (g :: l) = QCircuit.adj l ++ [(⟨⟨g.gate.arity, g.gate.matᴴ⟩,
        ⟨g.mem.1, by
          show g.gate.matᴴ ∈ Matrix.unitaryGroup _ ℂ
          rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem g.mem.2⟩, g.wires⟩ :
        GateApp allSmallGates N)] := by
      simp [QCircuit.adj]
    rw [h1, circuit_unitary_append, ih]
    have h2 : Circuit.unitary (g :: l) = Circuit.unitary l * embedOp g.gate.mat g.wires := by
      rw [show g :: l = [g] ++ l from rfl, circuit_unitary_append]
      simp [Circuit.unitary]
    rw [h2, Matrix.conjTranspose_mul, embedOp_conjTranspose]
    simp [Circuit.unitary]


/-! ## The X gate and `loadX` of one bit -/

def flipAt {n : ℕ} (a : Fin n) (z : Qubits n) : Qubits n :=
  fun k => if k = a then !z k else z k

theorem flipAt_invol {n : ℕ} (a : Fin n) (z : Qubits n) : flipAt a (flipAt a z) = z := by
  funext k; by_cases hk : k = a <;> simp [flipAt, hk]

theorem xGate_mem : (⟨1, permOf (N := 1) (flipAt 0)⟩ : Gate) ∈ allSmallGates :=
  ⟨by decide, permOf_unitary (N := 1) _ (flipAt_invol 0)⟩

def oneWire {n : ℕ} (a : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => a, fun i j _ => Subsingleton.elim i j⟩

def xGA {n : ℕ} (a : Fin n) : GateApp allSmallGates n :=
  ⟨⟨1, permOf (N := 1) (flipAt 0)⟩, xGate_mem, oneWire a⟩

theorem embedOp_xGA {n : ℕ} (a : Fin n) :
    embedOp (xGA a).gate.mat (xGA a).wires = permOf (flipAt a) := by
  ext y z
  show embedOp (permOf (N := 1) (flipAt 0)) (oneWire a) y z = permOf (flipAt a) y z
  simp only [embedOp, permOf, Matrix.of_apply]
  have hr : ∀ k : Fin n, k ∈ Set.range (oneWire a) ↔ k = a := by
    intro k; constructor
    · rintro ⟨i, hi⟩; exact hi.symm
    · rintro rfl; exact ⟨0, rfl⟩
  have hc : ((∀ k : Fin n, k ∉ Set.range (oneWire a) → y k = z k) ∧
      (y ∘ oneWire a = flipAt 0 (z ∘ oneWire a))) ↔ y = flipAt a z := by
    constructor
    · rintro ⟨hk, h2⟩
      have h0 := congrFun h2 0
      simp only [Function.comp_apply, flipAt, if_true] at h0
      funext k
      by_cases hka : k = a
      · subst hka; simp only [flipAt, if_true]; exact h0
      · simp only [flipAt, hka, if_false]; exact hk k (fun hh => hka ((hr k).1 hh))
    · intro hz; subst hz
      refine ⟨fun k hk => ?_, ?_⟩
      · have : k ≠ a := fun hh => hk ((hr k).2 hh)
        simp [flipAt, this]
      · funext i
        have : i = 0 := Subsingleton.elim _ _
        subst this
        simp [flipAt]; rfl
  by_cases H : y = flipAt a z
  · rw [if_pos (hc.2 H).1, if_pos (hc.2 H).2, if_pos H]
  · rw [if_neg H]
    by_cases H1 : ∀ k : Fin n, k ∉ Set.range (oneWire a) → y k = z k
    · rw [if_pos H1, if_neg (fun H2 => H (hc.1 ⟨H1, H2⟩))]
    · rw [if_neg H1]

/-- A circuit writing the one-bit message `[true]` into the wires `w`. -/
def flipCirc {n : ℕ} : List (Fin n) → QCircuit n
  | [] => []
  | a :: _ => [xGA a]

theorem flipCirc_unitary {n : ℕ} (w : List (Fin n)) :
    (flipCirc w).unitary = loadX w [true] := by
  cases w with
  | nil => simp [flipCirc, circuit_unitary_nil, loadX, flipMask]; ext y z; simp [Matrix.one_apply]
  | cons a rest =>
    show Circuit.unitary [xGA a] = loadX (a :: rest) [true]
    rw [show ([xGA a] : QCircuit n) = xGA a :: [] from rfl, circuit_unitary_cons, circuit_unitary_nil,
      one_mul, embedOp_xGA]
    ext y z
    simp only [permOf, loadX, Matrix.of_apply, flipMask, List.zip_cons_cons, List.zip_nil_right,
      List.any_cons, List.any_nil, Bool.or_false, Bool.and_true]
    have : flipAt a z = fun b => xor (z b) (decide (a = b)) := by
      funext b; by_cases hb : b = a
      · subst hb; simp [flipAt]
      · simp [flipAt, hb, Ne.symm hb]
    rw [this]

theorem flipCirc_size {n : ℕ} (w : List (Fin n)) : (flipCirc w).size ≤ 1 := by
  cases w <;> simp [flipCirc, Circuit.size]

theorem loadX_false {N : ℕ} (w : List (Fin N)) : loadX w [false] = 1 := by
  ext y z
  cases w with
  | nil => simp [loadX, flipMask, Matrix.one_apply]
  | cons a rest => simp [loadX, flipMask, Matrix.one_apply]

/-! ## Recording a prefix of the output wires onto fresh ancillas -/

section Rec
variable {N N' : ℕ}

/-- The record of the wires `dW`: their contents followed by one `false`. -/
def recVal (dW : List (Fin N)) (p : Qubits N) : Qubits (dW.length + 1) :=
  fun j => if hj : j.val < dW.length then p (dW.get ⟨j.val, hj⟩) else false

theorem ofFn_recVal (dW : List (Fin N)) (p : Qubits N) :
    List.ofFn (recVal dW p) = readWires dW p ++ [false] := by
  apply List.ext_getElem
  · simp [readWires]
  · intro i h1 h2
    simp only [List.getElem_ofFn, recVal]
    by_cases hi : i < dW.length
    · rw [dif_pos hi, List.getElem_append_left (by simpa [readWires] using hi)]
      simp [readWires]
    · rw [dif_neg hi, List.getElem_append_right (by simpa [readWires] using hi)]
      simp

def recGA {dW : List (Fin N)} (h : N + (dW.length + 1) = N') (j : Fin dW.length) :
    GateApp allSmallGates N' :=
  cnotGA (eL h (dW.get j)) (fL h (Fin.castSucc j)) (eL_ne_fL h _ _)

def recFun {dW : List (Fin N)} (h : N + (dW.length + 1) = N') :
    List (Fin dW.length) → Qubits N' → Qubits N'
  | [] => id
  | j :: l => recFun h l ∘ cnotFun (eL h (dW.get j)) (fL h (Fin.castSucc j))

theorem rec_unitary {dW : List (Fin N)} (h : N + (dW.length + 1) = N') (l : List (Fin dW.length)) :
    Circuit.unitary (l.map (recGA h)) = permOf (recFun h l) := by
  induction l with
  | nil => simp [circuit_unitary_nil, recFun, permOf_id]
  | cons j l ih =>
    rw [List.map_cons, circuit_unitary_cons, ih, recGA, embedOp_cnotGA, permOf_mul]
    rfl

theorem recFun_e {dW : List (Fin N)} (h : N + (dW.length + 1) = N') (l : List (Fin dW.length))
    (z : Qubits N') (i : Fin N) : recFun h l z (eL h i) = z (eL h i) := by
  induction l generalizing z with
  | nil => rfl
  | cons j l ih =>
    show recFun h l (cnotFun _ _ z) (eL h i) = _
    rw [ih]
    simp [cnotFun, eL_ne_fL]

theorem fL_inj {m : ℕ} (h : N + m = N') (a b : Fin m) : fL h a = fL h b ↔ a = b := by
  constructor
  · intro hh; have := congrArg Fin.val hh; simp [fL_val] at this; exact Fin.ext this
  · rintro rfl; rfl

theorem recFun_f {dW : List (Fin N)} (h : N + (dW.length + 1) = N') (l : List (Fin dW.length))
    (hl : l.Nodup) (z : Qubits N') (j : Fin (dW.length + 1)) :
    recFun h l z (fL h j) =
      if ∃ i ∈ l, Fin.castSucc i = j then xor (z (fL h j)) (recVal dW (z ∘ eL h) j)
      else z (fL h j) := by
  induction l generalizing z with
  | nil => simp [recFun]
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    show recFun h l (cnotFun _ _ z) (fL h j) = _
    rw [ih hl.2]
    have hval : ∀ (i : Fin dW.length) (z : Qubits N'), recVal dW (z ∘ eL h) (Fin.castSucc i) =
        z (eL h (dW.get i)) := by
      intro i z; simp [recVal]
    by_cases hjk : Fin.castSucc k = j
    · subst hjk
      have hn : ¬ ∃ i ∈ l, Fin.castSucc i = Fin.castSucc k := by
        rintro ⟨i, hi, hik⟩
        exact hl.1 (by rw [← Fin.castSucc_inj.1 hik]; exact hi)
      rw [if_neg hn, if_pos ⟨k, List.mem_cons_self, rfl⟩, hval]
      simp [cnotFun, eL_ne_fL]
    · have hjk' : fL h j ≠ fL h (Fin.castSucc k) := fun hh => hjk ((fL_inj h _ _).1 hh).symm
      have hiff : (∃ i ∈ k :: l, Fin.castSucc i = j) ↔ ∃ i ∈ l, Fin.castSucc i = j := by
        constructor
        · rintro ⟨i, hi, hij⟩
          rcases List.mem_cons.1 hi with rfl | hi
          · exact absurd hij hjk
          · exact ⟨i, hi, hij⟩
        · rintro ⟨i, hi, hij⟩; exact ⟨i, List.mem_cons_of_mem _ hi, hij⟩
      have he : (cnotFun (eL h (dW.get k)) (fL h (Fin.castSucc k)) z) ∘ eL h = z ∘ eL h := by
        funext i; simp [cnotFun, eL_ne_fL]
      rw [he]
      by_cases hjl : ∃ i ∈ l, Fin.castSucc i = j
      · rw [if_pos hjl, if_pos (hiff.2 hjl)]
        simp [cnotFun, hjk']
      · rw [if_neg hjl, if_neg (fun hh => hjl (hiff.1 hh))]
        simp [cnotFun, hjk']

/-- The record circuit. -/
def recCirc {dW : List (Fin N)} (h : N + (dW.length + 1) = N') : QCircuit N' :=
  (List.finRange dW.length).map (recGA h)

theorem recCirc_size {dW : List (Fin N)} (h : N + (dW.length + 1) = N') :
    (recCirc h).size = dW.length := by
  simp [recCirc, Circuit.size]

def recAll {dW : List (Fin N)} (h : N + (dW.length + 1) = N') : Qubits N' → Qubits N' :=
  recFun h (List.finRange dW.length)

theorem recAll_e {dW : List (Fin N)} (h : N + (dW.length + 1) = N') (z : Qubits N') :
    recAll h z ∘ eL h = z ∘ eL h := funext fun i => recFun_e h _ z i

theorem recAll_f {dW : List (Fin N)} (h : N + (dW.length + 1) = N') (z : Qubits N') :
    recAll h z ∘ fL h = fun j => xor (z (fL h j)) (recVal dW (z ∘ eL h) j) := by
  funext j
  simp only [Function.comp_apply, recAll]
  rw [recFun_f h _ (List.nodup_finRange _)]
  by_cases hj : j.val < dW.length
  · rw [if_pos ⟨⟨j.val, hj⟩, List.mem_finRange _, Fin.ext rfl⟩]
  · rw [if_neg]
    · simp [recVal, hj]
    · rintro ⟨i, _, hij⟩; exact hj (by rw [← hij]; simp)

theorem recAll_invol {dW : List (Fin N)} (h : N + (dW.length + 1) = N') (z : Qubits N') :
    recAll h (recAll h z) = z := by
  rw [eq_iff_split h]
  refine ⟨by rw [recAll_e, recAll_e], ?_⟩
  rw [recAll_f, recAll_e]
  funext j
  have := congrFun (recAll_f h z) j
  simp only [Function.comp_apply] at this ⊢
  rw [this]; simp

theorem recCirc_unitary {dW : List (Fin N)} (h : N + (dW.length + 1) = N') :
    (recCirc h).unitary = permOf (recAll h) := rec_unitary h _

/-- The recorded state: `recCirc (Y ⊗ |0⟩⟨0|) recCirc†`. -/
theorem rec_state {dW : List (Fin N)} (h : N + (dW.length + 1) = N')
    (Y : Matrix (Qubits N) (Qubits N) ℂ) (y z : Qubits N') :
    ((recCirc h).unitary * tens h Y (zeroDM (dW.length + 1)) * ((recCirc h).unitary)ᴴ) y z =
      Y (y ∘ eL h) (z ∘ eL h) * (if y ∘ fL h = recVal dW (y ∘ eL h) then 1 else 0) *
        (if z ∘ fL h = recVal dW (z ∘ eL h) then 1 else 0) := by
  rw [recCirc_unitary, permOf_conj_apply _ (recAll_invol h)]
  simp only [tens, zeroDM, Matrix.of_apply, recAll_e, recAll_f]
  have key : ∀ x : Qubits N', ((fun j => xor (x (fL h j)) (recVal dW (x ∘ eL h) j)) =
      fun _ => false) ↔ x ∘ fL h = recVal dW (x ∘ eL h) := by
    intro x; constructor
    · intro hh; funext j; have := congrFun hh j; simp only [Function.comp_apply]
      revert this; cases x (fL h j) <;> cases recVal dW (x ∘ eL h) j <;> simp
    · intro hh; funext j; have := congrFun hh j; simp only [Function.comp_apply] at this
      rw [this]; simp
  by_cases hy : y ∘ fL h = recVal dW (y ∘ eL h) <;>
    by_cases hz : z ∘ fL h = recVal dW (z ∘ eL h) <;>
    simp [hy, hz, key]

/-- A diagonal matrix reading only fresh wires commutes with an operator on the old wires. -/
theorem diag_fresh_comm {m : ℕ} (h : N + m = N') (f : Qubits m → ℂ)
    (A : Matrix (Qubits N) (Qubits N) ℂ) :
    Matrix.diagonal (fun z => f (z ∘ fL h)) * embedOp A (eL h) =
      embedOp A (eL h) * Matrix.diagonal (fun z => f (z ∘ fL h)) := by
  ext y z
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [embedOp, Matrix.of_apply]
  by_cases H : ∀ a : Fin N', a ∉ Set.range (eL h) → y a = z a
  · rw [if_pos H, (offRange_iff h y z).1 H, mul_comm]
  · rw [if_neg H]; simp

end Rec

section Toffoli
variable {N : ℕ}

/-- An operator on wire `t` depending (as a 2×2 matrix) on the other wires. -/
def Ctl (t : Fin N) (g : Qubits N → Matrix Bool Bool ℂ) : Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.of fun y z => if (∀ k, k ≠ t → y k = z k) then g z (y t) (z t) else 0

/-- `g` does not read wire `t`. -/
def NoT (t : Fin N) (g : Qubits N → Matrix Bool Bool ℂ) : Prop :=
  ∀ z c, g (Function.update z t c) = g z

theorem sum_offt (t : Fin N) (z : Qubits N) (F : Qubits N → ℂ)
    (hF : ∀ x, (∃ k, k ≠ t ∧ x k ≠ z k) → F x = 0) :
    ∑ x, F x = ∑ c : Bool, F (Function.update z t c) := by
  have hinj : Function.Injective (fun c : Bool => Function.update z t c) := by
    intro c d h; have := congrFun h t; simpa using this
  rw [← Finset.sum_image (s := Finset.univ) (fun c _ d _ h => hinj h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  apply hF
  by_contra hcon
  push_neg at hcon
  apply hx
  refine Finset.mem_image.2 ⟨x t, Finset.mem_univ _, ?_⟩
  funext k
  by_cases hk : k = t
  · subst hk; simp
  · rw [Function.update_of_ne hk, hcon k hk]

theorem Ctl_mul (t : Fin N) (g h : Qubits N → Matrix Bool Bool ℂ) (hg : NoT t g) (hh : NoT t h) :
    Ctl t g * Ctl t h = Ctl t (fun z => g z * h z) := by
  ext y z
  rw [Matrix.mul_apply]
  rw [sum_offt t z]
  · simp only [Ctl, Matrix.of_apply, Matrix.mul_apply]
    by_cases H : ∀ k, k ≠ t → y k = z k
    · rw [if_pos H]
      apply Finset.sum_congr rfl
      intro c _
      have h1 : ∀ k, k ≠ t → y k = Function.update z t c k := by
        intro k hk; rw [Function.update_of_ne hk]; exact H k hk
      have h2 : ∀ k, k ≠ t → Function.update z t c k = z k := by
        intro k hk; rw [Function.update_of_ne hk]
      rw [if_pos h1, if_pos h2, hg, Function.update_self]
    · rw [if_neg H]
      apply Finset.sum_eq_zero
      intro c _
      have h1 : ¬ ∀ k, k ≠ t → y k = Function.update z t c k := by
        intro hh; apply H; intro k hk; rw [hh k hk, Function.update_of_ne hk]
      rw [if_neg h1, zero_mul]
  · intro x ⟨k, hk, hx⟩
    simp only [Ctl, Matrix.of_apply]
    rw [if_neg (show ¬ ∀ k, k ≠ t → x k = z k from fun hh => hx (hh k hk)), mul_zero]

theorem Ctl_one (t : Fin N) : Ctl t (fun _ => 1) = 1 := by
  ext y z
  simp only [Ctl, Matrix.of_apply, Matrix.one_apply]
  by_cases H : ∀ k, k ≠ t → y k = z k
  · rw [if_pos H]
    by_cases ht : y t = z t
    · have : y = z := funext fun k => by
        by_cases hk : k = t
        · subst hk; exact ht
        · exact H k hk
      simp [this]
    · have : y ≠ z := fun h => ht (h ▸ rfl)
      simp [ht, this]
  · rw [if_neg H]
    have : y ≠ z := fun h => H (fun k _ => h ▸ rfl)
    simp [this]

theorem Ctl_conjTranspose (t : Fin N) (g : Qubits N → Matrix Bool Bool ℂ) (hg : NoT t g) :
    (Ctl t g)ᴴ = Ctl t (fun z => (g z)ᴴ) := by
  ext y z
  simp only [Ctl, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases H : ∀ k, k ≠ t → y k = z k
  · have H' : ∀ k, k ≠ t → z k = y k := fun k hk => (H k hk).symm
    rw [if_pos H, if_pos H']
    have : z = Function.update y t (z t) := by
      funext k
      by_cases hk : k = t
      · subst hk; simp
      · rw [Function.update_of_ne hk, H' k hk]
    rw [this, hg]
  · have H' : ¬ ∀ k, k ≠ t → z k = y k := fun hh => H (fun k hk => (hh k hk).symm)
    rw [if_neg H, if_neg H']; simp

/-- Permutation conjugation of a `Ctl` by an involution not touching `t`. -/
theorem permOf_Ctl_permOf (t : Fin N) (f : Qubits N → Qubits N) (hf : ∀ z, f (f z) = z)
    (hft : ∀ z c, f (Function.update z t c) = Function.update (f z) t c)
    (g : Qubits N → Matrix Bool Bool ℂ) :
    permOf f * Ctl t g * permOf f = Ctl t (fun z => g (f z)) := by
  ext y z
  have hc := permOf_conj_apply f hf (Ctl t g) y z
  rw [permOf_conjTranspose f hf] at hc
  rw [hc]
  simp only [Ctl, Matrix.of_apply]
  have ht : ∀ z, f z t = z t := by
    intro z
    have := congrFun (hft z (z t)) t
    rw [Function.update_eq_self] at this
    rw [this]; simp
  have key : (∀ k, k ≠ t → f y k = f z k) ↔ (∀ k, k ≠ t → y k = z k) := by
    have gen : ∀ y z : Qubits N, (∀ k, k ≠ t → y k = z k) → ∀ k, k ≠ t → f y k = f z k := by
      intro y z H k hk
      have hz : y = Function.update z t (y t) := by
        funext j
        by_cases hj : j = t
        · subst hj; simp
        · rw [Function.update_of_ne hj, H j hj]
      rw [hz, hft, Function.update_of_ne hk]
    constructor
    · intro H
      have := gen (f y) (f z) H
      simpa [hf] using this
    · exact gen y z
  by_cases H : ∀ k, k ≠ t → y k = z k
  · rw [if_pos (key.2 H), if_pos H, ht, ht]
  · rw [if_neg (fun hh => H (key.1 hh)), if_neg H]


/-- `V` with `V * V = X`. -/
noncomputable def Vm : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i = j then (1 + Complex.I) / 2 else (1 - Complex.I) / 2

def Xm : Matrix Bool Bool ℂ := Matrix.of fun i j => if i = j then 0 else 1

theorem Vm_mul_Vm : Vm * Vm = Xm := by
  ext i j
  cases i <;> cases j <;>
    simp [Vm, Xm, Matrix.mul_apply, Complex.ext_iff] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem Vm_mul_Vmh : Vm * Vmᴴ = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [Vm, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ext_iff, Matrix.one_apply] <;>
    ring_nf <;> norm_num

theorem Vmh_mul_Vm : Vmᴴ * Vm = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [Vm, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ext_iff, Matrix.one_apply] <;>
    ring_nf <;> norm_num

/-- Controlled-`W` on two qubits (control wire 0, target wire 1). -/
noncomputable def cMat (W : Matrix Bool Bool ℂ) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  Ctl (N := 2) 1 (fun z => if z 0 then W else 1)

theorem noT_if (t c : Fin N) (hct : c ≠ t) (W : Matrix Bool Bool ℂ) :
    NoT t (fun z => if z c then W else 1) := by
  intro z d; simp [Function.update_of_ne hct]

theorem cMat_unitary (W : Matrix Bool Bool ℂ) (hW : Wᴴ * W = 1) :
    cMat W ∈ Matrix.unitaryGroup (Qubits 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  show star (cMat W) * cMat W = 1
  rw [Matrix.star_eq_conjTranspose, cMat, Ctl_conjTranspose _ _ (noT_if 1 0 (by decide) W),
    Ctl_mul]
  · rw [← Ctl_one (N := 2) 1]
    congr 1; funext z
    by_cases h : z 0 <;> simp [h, hW]
  · intro z d; simp [Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  · exact noT_if 1 0 (by decide) W

theorem embedOp_cMat {n : ℕ} (a t : Fin n) (hat : a ≠ t) (W : Matrix Bool Bool ℂ) :
    embedOp (cMat W) (cnotWires a t hat) = Ctl t (fun z => if z a then W else 1) := by
  have hw0 : cnotWires a t hat 0 = a := rfl
  have hw1 : cnotWires a t hat 1 = t := rfl
  have hr : ∀ k, k ∈ Set.range (cnotWires a t hat) ↔ k = a ∨ k = t := by
    intro k; constructor
    · rintro ⟨i, rfl⟩; fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  ext y z
  simp only [embedOp, cMat, Ctl, Matrix.of_apply, Function.comp_apply]
  by_cases H : ∀ k, k ≠ t → y k = z k
  · have H1 : ∀ k, k ∉ Set.range (cnotWires a t hat) → y k = z k := by
      intro k hk; rw [hr] at hk; push_neg at hk; exact H k hk.2
    have H2 : ∀ k : Fin 2, k ≠ 1 → y (cnotWires a t hat k) = z (cnotWires a t hat k) := by
      intro k hk; fin_cases k
      · exact H a hat
      · exact absurd rfl hk
    rw [if_pos H1, if_pos H2, if_pos H]
    rfl
  · rw [if_neg H]
    by_cases H1 : ∀ k, k ∉ Set.range (cnotWires a t hat) → y k = z k
    · rw [if_pos H1]
      have H2 : ¬ ∀ k : Fin 2, k ≠ 1 → y (cnotWires a t hat k) = z (cnotWires a t hat k) := by
        intro hh
        apply H
        intro k hk
        by_cases hka : k = a
        · subst hka; exact hh 0 (by decide)
        · exact H1 k (by rw [hr]; push_neg; exact ⟨hka, hk⟩)
      rw [if_neg H2]
    · rw [if_neg H1]

noncomputable def cGate (W : Matrix Bool Bool ℂ) (hW : Wᴴ * W = 1) : Gate := ⟨2, cMat W⟩

theorem cGate_mem (W : Matrix Bool Bool ℂ) (hW : Wᴴ * W = 1) : cGate W hW ∈ allSmallGates :=
  ⟨le_refl _, cMat_unitary W hW⟩

noncomputable def cGA {n : ℕ} (W : Matrix Bool Bool ℂ) (hW : Wᴴ * W = 1) (a t : Fin n)
    (hat : a ≠ t) : GateApp allSmallGates n :=
  ⟨cGate W hW, cGate_mem W hW, cnotWires a t hat⟩

theorem Vmh_h : Vmᴴᴴ * Vmᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact Vm_mul_Vmh

/-- Toffoli on basis states. -/
def toffFun {n : ℕ} (a b t : Fin n) (x : Qubits n) : Qubits n :=
  Function.update x t (xor (x t) (x a && x b))

/-- Barenco et al.: Toffoli from controlled-`V`, CNOT, controlled-`V†`. -/
noncomputable def toffCirc {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    QCircuit n :=
  [cGA Vm Vmh_mul_Vm b t hbt, cnotGA a b hab, cGA Vmᴴ Vmh_h b t hbt, cnotGA a b hab,
    cGA Vm Vmh_mul_Vm a t hat]

theorem Ctl_toff {n : ℕ} (a b t : Fin n) (hat : a ≠ t) (hbt : b ≠ t) :
    Ctl t (fun z => if (z a && z b) then Xm else 1) = permOf (toffFun a b t) := by
  ext y z
  simp only [Ctl, permOf, Matrix.of_apply]
  by_cases H : ∀ k, k ≠ t → y k = z k
  · rw [if_pos H]
    have hiff : y = toffFun a b t z ↔ y t = xor (z t) (z a && z b) := by
      constructor
      · intro h; rw [h]; simp [toffFun]
      · intro h; funext k
        by_cases hk : k = t
        · subst hk; simp [toffFun, h]
        · simp only [toffFun]; rw [Function.update_of_ne hk, H k hk]
    by_cases hc : (z a && z b) = true
    · rw [if_pos hc]
      show (if y t = z t then (0:ℂ) else 1) = _
      by_cases h : y t = z t
      · rw [if_pos h, if_neg]; rw [hiff, hc, h]; cases z t <;> simp
      · rw [if_neg h, if_pos]; rw [hiff, hc]; revert h; cases y t <;> cases z t <;> simp
    · rw [if_neg hc]
      have hc' : (z a && z b) = false := by simpa using hc
      rw [Matrix.one_apply]
      by_cases h : y t = z t
      · rw [if_pos h, if_pos (hiff.2 (by rw [hc', Bool.xor_false]; exact h))]
      · rw [if_neg h, if_neg (fun hh => h (by rw [hiff.1 hh, hc', Bool.xor_false]))]
  · rw [if_neg H, if_neg]
    intro hy; apply H; intro k hk; rw [hy]; simp [toffFun, Function.update_of_ne hk]

theorem toffCirc_unitary {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    (toffCirc a b t hab hat hbt).unitary = permOf (toffFun a b t) := by
  have e1 : ∀ (W : Matrix Bool Bool ℂ) (hW : Wᴴ * W = 1) (c : Fin n) (hct : c ≠ t),
      embedOp (cGA W hW c t hct).gate.mat (cGA W hW c t hct).wires =
        Ctl t (fun z => if z c then W else 1) := fun W hW c hct => embedOp_cMat c t hct W
  have hcn : ∀ z d, cnotFun a b (Function.update z t d) = Function.update (cnotFun a b z) t d := by
    intro z d; funext k
    by_cases hk : k = t
    · subst hk; simp [cnotFun, hbt.symm]
    · rw [Function.update_of_ne hk]
      by_cases hkb : k = b
      · subst hkb; simp [cnotFun, Function.update_of_ne hbt, Function.update_of_ne hat]
      · simp [cnotFun, hkb, Function.update_of_ne hk]
  simp only [toffCirc, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
  rw [e1, e1, e1, embedOp_cnotGA]
  have hmid : permOf (cnotFun a b) * (Ctl t (fun z => if z b then Vmᴴ else 1) *
      (permOf (cnotFun a b) * Ctl t (fun z => if z b then Vm else 1))) =
      Ctl t (fun z => if (cnotFun a b z) b then Vmᴴ else 1) * Ctl t (fun z => if z b then Vm else 1) := by
    rw [← mul_assoc, ← mul_assoc, permOf_Ctl_permOf t _ (cnotFun_invol a b hab) hcn]
  rw [hmid, Ctl_mul, Ctl_mul, ← Ctl_toff a b t hat hbt]
  · congr 1; funext z
    simp only [cnotFun, if_true]
    cases z a <;> cases z b <;> simp [Vm_mul_Vm, Vmh_mul_Vm, Vm_mul_Vmh, ← mul_assoc]
  · exact noT_if t a hat Vm
  · intro z d
    simp only [cnotFun, if_true]
    simp [Function.update_of_ne hat, Function.update_of_ne hbt]
  · intro z d
    simp only [cnotFun, if_true]
    simp [Function.update_of_ne hat, Function.update_of_ne hbt]
  · exact noT_if t b hbt Vm

theorem toffCirc_size {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    (toffCirc a b t hab hat hbt).size = 5 := rfl

end Toffoli

section MCX
variable {n : ℕ}

/-- `c` realises the basis permutation `f`. -/
def Realizes (c : QCircuit n) (f : Qubits n → Qubits n) : Prop := c.unitary = permOf f

theorem realizes_nil : Realizes ([] : QCircuit n) id := by
  rw [Realizes, circuit_unitary_nil, permOf_id]

theorem realizes_append {c₁ c₂ : QCircuit n} {f₁ f₂ : Qubits n → Qubits n}
    (h₁ : Realizes c₁ f₁) (h₂ : Realizes c₂ f₂) : Realizes (c₁ ++ c₂) (f₂ ∘ f₁) := by
  rw [Realizes, circuit_unitary_append, h₁, h₂, permOf_mul]

theorem realizes_x (a : Fin n) : Realizes [xGA a] (flipAt a) := by
  rw [Realizes, circuit_unitary_cons, circuit_unitary_nil, Matrix.one_mul, embedOp_xGA]

theorem realizes_cnot (a t : Fin n) (h : a ≠ t) : Realizes [cnotGA a t h] (cnotFun a t) := by
  rw [Realizes, circuit_unitary_cons, circuit_unitary_nil, Matrix.one_mul, embedOp_cnotGA]

theorem realizes_toff (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Realizes (toffCirc a b t hab hat hbt) (toffFun a b t) := toffCirc_unitary a b t hab hat hbt

/-- XOR the bit `v z` into wire `t`. -/
def xorAt (t : Fin n) (v : Qubits n → Bool) (z : Qubits n) : Qubits n :=
  Function.update z t (xor (z t) (v z))

/-- Pattern test: every control wire `c` has value `b`. -/
def patOK (cs : List (Fin n × Bool)) (z : Qubits n) : Bool := cs.all fun p => z p.1 == p.2

def xIf (a : Fin n) (α : Bool) : QCircuit n := if α then [] else [xGA a]

def flipIf (a : Fin n) (α : Bool) : Qubits n → Qubits n := if α then id else flipAt a

theorem realizes_xIf (a : Fin n) (α : Bool) : Realizes (xIf a α) (flipIf a α) := by
  cases α
  · exact realizes_x a
  · exact realizes_nil

/-- Single control with polarity. -/
noncomputable def cnotP (a : Fin n) (α : Bool) (t : Fin n) : QCircuit n :=
  if h : a ≠ t then xIf a α ++ [cnotGA a t h] ++ xIf a α else []

theorem realizes_cnotP (a : Fin n) (α : Bool) (t : Fin n) (h : a ≠ t) :
    Realizes (cnotP a α t) (xorAt t (fun z => z a == α)) := by
  have hr := realizes_append (realizes_append (realizes_xIf a α) (realizes_cnot a t h))
    (realizes_xIf a α)
  rw [cnotP, dif_pos h]
  convert hr using 1
  funext z; funext k
  cases α <;> by_cases hk : k = t <;> by_cases hka : k = a <;>
    simp_all [flipIf, flipAt, cnotFun, xorAt, Function.update, h, Ne.symm h]

/-- Toffoli with polarities. -/
noncomputable def toffP (a : Fin n) (α : Bool) (b : Fin n) (β : Bool) (t : Fin n) : QCircuit n :=
  if h : a ≠ b ∧ a ≠ t ∧ b ≠ t then
    xIf a α ++ xIf b β ++ toffCirc a b t h.1 h.2.1 h.2.2 ++ xIf a α ++ xIf b β
  else []

theorem realizes_toffP (a : Fin n) (α : Bool) (b : Fin n) (β : Bool) (t : Fin n)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Realizes (toffP a α b β t) (xorAt t (fun z => (z a == α) && (z b == β))) := by
  have hr := realizes_append (realizes_append (realizes_append (realizes_append
    (realizes_xIf a α) (realizes_xIf b β)) (realizes_toff a b t hab hat hbt))
    (realizes_xIf a α)) (realizes_xIf b β)
  rw [toffP, dif_pos ⟨hab, hat, hbt⟩]
  convert hr using 1
  funext z; funext k
  cases α <;> cases β <;> by_cases hk : k = t <;> by_cases hka : k = a <;> by_cases hkb : k = b <;>
    simp_all [flipIf, flipAt, toffFun, xorAt, Function.update, Ne.symm hab, Ne.symm hat,
      Ne.symm hbt]

/-- Multi-controlled X with a pattern, using clean ancillas `anc`. -/
noncomputable def mcx : List (Fin n × Bool) → Fin n → List (Fin n) → QCircuit n
  | [], t, _ => [xGA t]
  | [(c, α)], t, _ => cnotP c α t
  | (c₁, α₁) :: (c₂, α₂) :: rest, t, anc =>
      match anc with
      | [] => []
      | a :: anc' => toffP c₁ α₁ c₂ α₂ a ++ mcx ((a, true) :: rest) t anc' ++ toffP c₁ α₁ c₂ α₂ a

theorem mcx_spec : ∀ (cs : List (Fin n × Bool)) (t : Fin n) (anc : List (Fin n)),
    (t :: (cs.map Prod.fst ++ anc)).Nodup → cs.length ≤ anc.length + 1 →
    ∃ F, Realizes (mcx cs t anc) F ∧
      ∀ z, (∀ a ∈ anc, z a = false) → F z = xorAt t (patOK cs) z
  | [], t, anc, _, _ => ⟨flipAt t, by simp only [mcx]; exact realizes_x t, fun z _ => by
      funext k; by_cases hk : k = t <;> simp [flipAt, xorAt, patOK, hk, Function.update]⟩
  | [(c, α)], t, anc, hnd, _ => by
      have hct : c ≠ t := by
        intro h; subst h; simp at hnd
      refine ⟨_, by simp only [mcx]; exact realizes_cnotP c α t hct, fun z _ => ?_⟩
      simp [xorAt, patOK]
  | (c₁, α₁) :: (c₂, α₂) :: rest, t, anc, hnd, hlen => by
      match anc, hnd, hlen with
      | [], _, hlen => simp at hlen
      | a :: anc', hnd, hlen =>
        simp only [List.map_cons, List.cons_append] at hnd
        have hX : (t :: (rest.map Prod.fst ++ a :: anc')).Nodup :=
          hnd.sublist (List.Sublist.cons₂ t
            ((List.sublist_cons_self _ _).trans (List.sublist_cons_self _ _)))
        have hnd' : (t :: (a :: (rest.map Prod.fst ++ anc'))).Nodup := by
          rw [List.nodup_cons] at hX ⊢
          exact ⟨fun h => hX.1 (List.perm_middle.mem_iff.2 h), List.nodup_middle.1 hX.2⟩
        have hta : t ≠ a := fun h => (List.nodup_cons.1 hnd').1 (h ▸ List.mem_cons_self)
        have ha2 := (List.nodup_cons.1 (List.nodup_cons.1 hnd').2).1
        have hra : ∀ p ∈ rest, p.1 ≠ a := by
          intro p hp h; apply ha2; rw [← h]
          exact List.mem_append_left _ (List.mem_map_of_mem hp)
        have haanc : a ∉ anc' := fun h => ha2 (List.mem_append_right _ h)
        have h12 : c₁ ≠ c₂ := by rintro rfl; simp at hnd
        have h1a : c₁ ≠ a := by rintro rfl; simp at hnd
        have h2a : c₂ ≠ a := by rintro rfl; simp at hnd
        have h1t : c₁ ≠ t := by rintro rfl; simp at hnd
        have h2t : c₂ ≠ t := by rintro rfl; simp at hnd
        obtain ⟨F', hF', hF'z⟩ := mcx_spec ((a, true) :: rest) t anc' (by simpa using hnd')
          (by simpa using hlen)
        have hT := realizes_toffP c₁ α₁ c₂ α₂ a h12 h1a h2a
        refine ⟨_, by simp only [mcx]; exact realizes_append (realizes_append hT hF') hT,
          fun z hz => ?_⟩
        have hza : z a = false := hz a List.mem_cons_self
        simp only [Function.comp_apply]
        set m := (z c₁ == α₁) && (z c₂ == α₂) with hm
        set z' := xorAt a (fun z => (z c₁ == α₁) && (z c₂ == α₂)) z with hz'
        have hz'a : z' a = m := by simp [hz', xorAt, hza, hm]
        have hz'o : ∀ k, k ≠ a → z' k = z k := by
          intro k hk; simp [hz', xorAt, Function.update_of_ne hk]
        have hcl : ∀ b ∈ anc', z' b = false := by
          intro b hb
          rw [hz'o b (fun h => haanc (h ▸ hb))]
          exact hz b (List.mem_cons_of_mem _ hb)
        rw [hF'z z' hcl]
        have hpr : patOK rest z' = patOK rest z := by
          rw [Bool.eq_iff_iff]; simp only [patOK, List.all_eq_true]
          exact ⟨fun H p hp => by rw [← hz'o p.1 (hra p hp)]; exact H p hp,
            fun H p hp => by rw [hz'o p.1 (hra p hp)]; exact H p hp⟩
        have hpa : patOK ((a, true) :: rest) z' = (m && patOK rest z) := by
          rw [← hpr]; simp [patOK, hz'a]
        set y := xorAt t (patOK ((a, true) :: rest)) z' with hy
        have hyt : y t = xor (z t) (m && patOK rest z) := by
          rw [hy, xorAt, Function.update_self, hpa, hz'o t hta]
        have hyo : ∀ k, k ≠ t → y k = z' k := by
          intro k hk; simp [hy, xorAt, Function.update_of_ne hk]
        have hy1 : y c₁ = z c₁ := by rw [hyo _ h1t, hz'o _ h1a]
        have hy2 : y c₂ = z c₂ := by rw [hyo _ h2t, hz'o _ h2a]
        funext k
        simp only [xorAt]
        by_cases hka : k = a
        · subst hka
          rw [Function.update_self, Function.update_of_ne (Ne.symm hta), hyo _ (Ne.symm hta),
            hz'a, hy1, hy2, hza]
          simp [hm]
        · rw [Function.update_of_ne hka]
          by_cases hkt : k = t
          · subst hkt
            rw [hyt, Function.update_self]
            simp [patOK, hm, Bool.and_assoc]
          · rw [hyo _ hkt, hz'o _ hka, Function.update_of_ne hkt]

end MCX

section Jobs
variable {n : ℕ}

abbrev Job (n : ℕ) := List (Fin n × Bool) × Fin n

noncomputable def jobsCirc (jobs : List (Job n)) (anc : List (Fin n)) : QCircuit n :=
  jobs.flatMap fun j => mcx j.1 j.2 anc

def jobsFun (jobs : List (Job n)) (z : Qubits n) : Qubits n :=
  jobs.foldl (fun z j => xorAt j.2 (patOK j.1) z) z

/-- The XOR written into wire `k` by the jobs, evaluated on the controls of `z`. -/
def eff (jobs : List (Job n)) (z : Qubits n) (k : Fin n) : Bool :=
  jobs.foldr (fun j acc => xor (decide (j.2 = k) && patOK j.1 z) acc) false

theorem eff_append (l₁ l₂ : List (Job n)) (z : Qubits n) (k : Fin n) :
    eff (l₁ ++ l₂) z k = xor (eff l₁ z k) (eff l₂ z k) := by
  induction l₁ with
  | nil => simp [eff]
  | cons j l ih => simp only [eff, List.cons_append, List.foldr_cons] at ih ⊢; rw [ih]; simp

theorem eff_nil (z : Qubits n) (k : Fin n) : eff ([] : List (Job n)) z k = false := rfl

theorem eff_cons (j : Job n) (l : List (Job n)) (z : Qubits n) (k : Fin n) :
    eff (j :: l) z k = xor (decide (j.2 = k) && patOK j.1 z) (eff l z k) := rfl

theorem patOK_congr (cs : List (Fin n × Bool)) (y z : Qubits n) (h : ∀ c ∈ cs, y c.1 = z c.1) :
    patOK cs y = patOK cs z := by
  rw [Bool.eq_iff_iff]; simp only [patOK, List.all_eq_true]
  exact ⟨fun H p hp => by rw [← h p hp]; exact H p hp, fun H p hp => by rw [h p hp]; exact H p hp⟩

theorem jobsFun_cons (j : Job n) (l : List (Job n)) (z : Qubits n) :
    jobsFun (j :: l) z = jobsFun l (xorAt j.2 (patOK j.1) z) := rfl

theorem jobsFun_clean (l : List (Job n)) (anc : List (Fin n)) (hl : ∀ j ∈ l, j.2 ∉ anc) :
    ∀ z : Qubits n, (∀ a ∈ anc, z a = false) → ∀ a ∈ anc, jobsFun l z a = false := by
  induction l with
  | nil => exact fun z hz => hz
  | cons j l ih =>
    intro z hz
    rw [jobsFun_cons]
    apply ih (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'))
    intro a ha
    have ha' : a ≠ j.2 := fun h => hl j List.mem_cons_self (h ▸ ha)
    rw [xorAt, Function.update_of_ne ha']
    exact hz a ha

theorem jobs_spec (jobs : List (Job n)) (anc : List (Fin n))
    (hj : ∀ j ∈ jobs, (j.2 :: (j.1.map Prod.fst ++ anc)).Nodup ∧ j.1.length ≤ anc.length + 1) :
    ∃ F, Realizes (jobsCirc jobs anc) F ∧
      ∀ z, (∀ a ∈ anc, z a = false) → F z = jobsFun jobs z := by
  induction jobs with
  | nil => exact ⟨id, realizes_nil, fun z _ => rfl⟩
  | cons j l ih =>
    obtain ⟨F, hF, hFz⟩ := ih (fun j' hj' => hj j' (List.mem_cons_of_mem _ hj'))
    obtain ⟨G, hG, hGz⟩ := mcx_spec j.1 j.2 anc (hj j List.mem_cons_self).1
      (hj j List.mem_cons_self).2
    refine ⟨F ∘ G, ?_, fun z hz => ?_⟩
    · have := realizes_append hG hF
      simpa [jobsCirc, List.flatMap_cons] using this
    · have hnd := (hj j List.mem_cons_self).1
      have hta : j.2 ∉ anc := fun h => (List.nodup_cons.1 hnd).1 (List.mem_append_right _ h)
      have hcl : ∀ a ∈ anc, G z a = false := by
        intro a ha
        rw [hGz z hz, xorAt, Function.update_of_ne (fun (h : a = j.2) => hta (h ▸ ha))]
        exact hz a ha
      rw [Function.comp_apply, hFz _ hcl, hGz z hz, jobsFun_cons]

theorem eff_congr (l : List (Job n)) (y z : Qubits n) (h : ∀ j ∈ l, ∀ c ∈ j.1, y c.1 = z c.1)
    (k : Fin n) : eff l y k = eff l z k := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [eff_cons, eff_cons, ih (fun j' hj' => h j' (List.mem_cons_of_mem _ hj')),
      patOK_congr j.1 y z (h j List.mem_cons_self)]

/-- If no control of the jobs is a target of the jobs, they XOR `eff` into `z`. -/
theorem jobsFun_eq (jobs : List (Job n)) (hd : ∀ j ∈ jobs, ∀ j' ∈ jobs, ∀ c ∈ j.1, c.1 ≠ j'.2)
    (z : Qubits n) (k : Fin n) : jobsFun jobs z k = xor (z k) (eff jobs z k) := by
  induction jobs generalizing z with
  | nil => simp [jobsFun, eff]
  | cons j l ih =>
    have ih' := ih (fun a ha b hb => hd a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    rw [jobsFun_cons, ih', eff_cons]
    have hl : eff l (xorAt j.2 (patOK j.1) z) k = eff l z k := by
      apply eff_congr
      intro j' hj' c hc
      rw [xorAt, Function.update_of_ne (hd j' (List.mem_cons_of_mem _ hj') j List.mem_cons_self c hc)]
    rw [hl]
    by_cases hk : j.2 = k
    · subst hk; simp [xorAt]
    · simp [xorAt, Function.update_of_ne (Ne.symm hk), hk]

end Jobs

section Decode
variable {n : ℕ}

def flatBits (x : Bits) : Bits := x.flatMap fun b => [true, b]

theorem packOne_getD (x : Bits) (i : ℕ) : (packOne x).getD i false = (flatBits x).getD i false := by
  show (flatBits x ++ [false]).getD i false = _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with hi
  · rfl
  · rw [List.getElem?_eq_none (by omega : (flatBits x).length ≤ i)]
    rcases (i - (flatBits x).length) with _ | k <;> simp

def termJobs (tgt : ℕ → Fin n) (P : List (Fin n × Bool)) : List (Fin n) → List (Job n)
  | [] => []
  | d :: ds => (P, tgt 0) :: (P ++ [(d, true)], tgt 1) :: termJobs (fun i => tgt (i + 2)) P ds

def dJobs (tgt : ℕ → Fin n) : List (Fin n × Bool) → List (Fin n) → List (Fin n) → List (Job n)
  | pre, ds, f :: d :: rest =>
      termJobs tgt (pre ++ [(f, false)]) ds ++ dJobs tgt (pre ++ [(f, true)]) (ds ++ [d]) rest
  | pre, ds, [f] => termJobs tgt (pre ++ [(f, false)]) ds
  | _, _, [] => []

theorem patOK_append (a b : List (Fin n × Bool)) (z : Qubits n) :
    patOK (a ++ b) z = (patOK a z && patOK b z) := by simp [patOK, List.all_append]

theorem patOK_single (c : Fin n) (b : Bool) (z : Qubits n) : patOK [(c, b)] z = (z c == b) := by
  simp [patOK]

theorem eff_notarget (l : List (Job n)) (z : Qubits n) (k : Fin n) (h : ∀ j ∈ l, j.2 ≠ k) :
    eff l z k = false := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [eff_cons, ih (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))]
    simp [h j List.mem_cons_self]

theorem eff_prefix_false (l : List (Job n)) (z : Qubits n) (k : Fin n) (P : List (Fin n × Bool))
    (hP : patOK P z = false) (h : ∀ j ∈ l, ∃ Q, j.1 = P ++ Q) : eff l z k = false := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [eff_cons, ih (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))]
    obtain ⟨Q, hQ⟩ := h j List.mem_cons_self
    simp [hQ, patOK_append, hP]

theorem termJobs_prefix (tgt : ℕ → Fin n) (P : List (Fin n × Bool)) (ds : List (Fin n)) :
    ∀ j ∈ termJobs tgt P ds, ∃ Q, j.1 = P ++ Q := by
  induction ds generalizing tgt with
  | nil => simp [termJobs]
  | cons d ds ih =>
    intro j hj
    simp only [termJobs, List.mem_cons] at hj
    rcases hj with rfl | rfl | hj
    · exact ⟨[], by simp⟩
    · exact ⟨_, rfl⟩
    · exact ih _ j hj

def InjBelow (tgt : ℕ → Fin n) (M : ℕ) : Prop :=
  ∀ a b, a < M → b < M → tgt a = tgt b → a = b

theorem InjBelow.shift {tgt : ℕ → Fin n} {M : ℕ} (h : InjBelow tgt M) (s : ℕ) :
    InjBelow (fun i => tgt (i + s)) (M - s) := by
  intro a b ha hb hab; have := h (a + s) (b + s) (by omega) (by omega) hab; omega

theorem termJobs_tgt (tgt : ℕ → Fin n) (P : List (Fin n × Bool)) (ds : List (Fin n)) :
    ∀ j ∈ termJobs tgt P ds, ∃ i, i < 2 * ds.length ∧ j.2 = tgt i := by
  induction ds generalizing tgt with
  | nil => simp [termJobs]
  | cons d ds ih =>
    intro j hj
    simp only [termJobs, List.mem_cons] at hj
    rcases hj with rfl | rfl | hj
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp; omega, rfl⟩
    · obtain ⟨i, hi, hi'⟩ := ih _ j hj; exact ⟨i + 2, by simp; omega, hi'⟩

theorem eff_termJobs (tgt : ℕ → Fin n) (M : ℕ) (htgt : InjBelow tgt M) (P : List (Fin n × Bool))
    (ds : List (Fin n)) (hM : 2 * ds.length ≤ M) (z : Qubits n) (i : ℕ) (hi : i < M) :
    eff (termJobs tgt P ds) z (tgt i) = (patOK P z && (flatBits (ds.map z)).getD i false) := by
  induction ds generalizing tgt i M with
  | nil => simp [termJobs, eff, flatBits]
  | cons d ds ih =>
    simp only [List.length_cons] at hM
    rw [termJobs, eff_cons, eff_cons]
    have h10 : tgt 1 ≠ tgt 0 := fun h => by have := htgt 1 0 (by omega) (by omega) h; omega
    have hne : ∀ j ∈ termJobs (fun i => tgt (i + 2)) P ds, ∀ i', i' < 2 → j.2 ≠ tgt i' := by
      intro j hj i' hi' h
      obtain ⟨k, hk, hk'⟩ := termJobs_tgt _ P ds j hj
      rw [hk'] at h
      have := htgt _ _ (by omega) (by omega) h; omega
    rcases i with _ | _ | i
    · rw [eff_notarget _ _ _ (fun j hj => hne j hj 0 (by omega))]
      simp [flatBits, h10]
    · rw [eff_notarget _ _ _ (fun j hj => hne j hj 1 (by omega))]
      simp [flatBits, patOK_append, patOK_single, Ne.symm h10]
    · have h2 : eff (termJobs (fun i => tgt (i + 2)) P ds) z (tgt (i + 2)) = _ :=
        ih (fun i => tgt (i + 2)) (M - 2) (htgt.shift 2) (by omega) i (by omega)
      rw [h2]
      have e0 : tgt 0 ≠ tgt (i + 2) := fun h => by have := htgt _ _ (by omega) hi h; omega
      have e1 : tgt 1 ≠ tgt (i + 2) := fun h => by have := htgt _ _ (by omega) hi h; omega
      simp [flatBits, e0, e1]

theorem dJobs_prefix (tgt : ℕ → Fin n) : ∀ (pre : List (Fin n × Bool)) (ds ws : List (Fin n)),
    ∀ j ∈ dJobs tgt pre ds ws, ∃ Q, j.1 = pre ++ Q
  | pre, ds, f :: d :: rest => by
      intro j hj
      rw [dJobs, List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨Q, hQ⟩ := termJobs_prefix tgt _ ds j hj; exact ⟨(f, false) :: Q, by simp [hQ]⟩
      · obtain ⟨Q, hQ⟩ := dJobs_prefix tgt _ _ rest j hj; exact ⟨(f, true) :: Q, by simp [hQ]⟩
  | pre, ds, [f] => by
      intro j hj
      rw [dJobs] at hj
      obtain ⟨Q, hQ⟩ := termJobs_prefix tgt _ ds j hj; exact ⟨(f, false) :: Q, by simp [hQ]⟩
  | pre, ds, [] => by simp [dJobs]

theorem eff_dJobs (tgt : ℕ → Fin n) (M : ℕ) (htgt : InjBelow tgt M) (z : Qubits n) (i : ℕ)
    (hi : i < M) :
    ∀ (pre : List (Fin n × Bool)) (ds ws : List (Fin n)), 2 * ds.length + ws.length ≤ M →
      patOK pre z = true →
      eff (dJobs tgt pre ds ws) z (tgt i) =
        match unpackAux (ws.map z) (ds.map z).reverse with
        | [] => false
        | x :: _ => (flatBits x).getD i false
  | pre, ds, f :: d :: rest, hM, hpre => by
      simp only [List.length_cons] at hM
      rw [dJobs, eff_append, eff_termJobs tgt M htgt _ ds (by omega) z i hi]
      cases hf : z f
      · rw [eff_prefix_false _ z _ (pre ++ [(f, true)]) (by simp [patOK_append, patOK_single, hf])
          (dJobs_prefix tgt _ _ rest)]
        simp [patOK_append, hpre, patOK_single, hf, unpackAux]
      · rw [eff_dJobs tgt M htgt z i hi (pre ++ [(f, true)]) (ds ++ [d]) rest (by simp; omega)
          (by simp [patOK_append, hpre, patOK_single, hf])]
        simp [patOK_append, hpre, patOK_single, hf, unpackAux]
  | pre, ds, [f], hM, hpre => by
      simp only [List.length_cons, List.length_nil] at hM
      rw [dJobs, eff_termJobs tgt M htgt _ ds (by omega) z i hi]
      cases hf : z f <;> simp [patOK_append, hpre, patOK_single, hf, unpackAux]
  | pre, ds, [], hM, hpre => by simp [dJobs, eff, unpackAux]

end Decode

section Encode
variable {n : ℕ}

/-- The bits `dJobs` writes, as a function of the read string. -/
def dOut (w : Bits) (i : ℕ) : Bool :=
  match unpackAux w [] with
  | [] => false
  | x :: _ => (flatBits x).getD i false

theorem dOut_eq (w : Bits) (i : ℕ) : dOut w i = (packOne (decodeOne w)).getD i false := by
  rw [packOne_getD, dOut, decodeOne, unpack]
  cases unpackAux w [] with
  | nil => simp [flatBits]
  | cons x _ => rfl

theorem eff_dJobs_top (tgt : ℕ → Fin n) (M : ℕ) (htgt : InjBelow tgt M) (z : Qubits n)
    (ws : List (Fin n)) (hM : ws.length ≤ M) (i : ℕ) (hi : i < M) :
    eff (dJobs tgt [] [] ws) z (tgt i) = (packOne (decodeOne (ws.map z))).getD i false := by
  rw [eff_dJobs tgt M htgt z i hi [] [] ws (by simpa using hM) rfl, ← dOut_eq]
  rfl

def eJobs (tgt : ℕ → Fin n) : List (Fin n × Bool) → List (Fin n) → List (Fin n) → List (Job n)
  | pre, rf :: _ :: rrest, ws =>
      dJobs (fun i => tgt (i + 1)) (pre ++ [(rf, false)]) [] ws ++
        eJobs (fun i => tgt (i + 2)) (pre ++ [(rf, true)]) rrest ws
  | pre, [rf], ws => dJobs (fun i => tgt (i + 1)) (pre ++ [(rf, false)]) [] ws
  | _, [], _ => []

theorem eJobs_prefix (tgt : ℕ → Fin n) : ∀ (pre : List (Fin n × Bool)) (rws ws : List (Fin n)),
    ∀ j ∈ eJobs tgt pre rws ws, ∃ Q, j.1 = pre ++ Q
  | pre, rf :: rd :: rrest, ws => by
      intro j hj
      rw [eJobs, List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨Q, hQ⟩ := dJobs_prefix _ _ _ ws j hj; exact ⟨(rf, false) :: Q, by simp [hQ]⟩
      · obtain ⟨Q, hQ⟩ := eJobs_prefix _ _ rrest ws j hj; exact ⟨(rf, true) :: Q, by simp [hQ]⟩
  | pre, [rf], ws => by
      intro j hj
      rw [eJobs] at hj
      obtain ⟨Q, hQ⟩ := dJobs_prefix _ _ _ ws j hj; exact ⟨(rf, false) :: Q, by simp [hQ]⟩
  | pre, [], ws => by simp [eJobs]

theorem dJobs_tgt (tgt : ℕ → Fin n) : ∀ (pre : List (Fin n × Bool)) (ds ws : List (Fin n)),
    ∀ j ∈ dJobs tgt pre ds ws, ∃ i, i < 2 * ds.length + ws.length ∧ j.2 = tgt i
  | pre, ds, f :: d :: rest => by
      intro j hj
      rw [dJobs, List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨i, hi, h⟩ := termJobs_tgt tgt _ ds j hj; exact ⟨i, by simp; omega, h⟩
      · obtain ⟨i, hi, h⟩ := dJobs_tgt tgt _ _ rest j hj; exact ⟨i, by simp at hi ⊢; omega, h⟩
  | pre, ds, [f] => by
      intro j hj; rw [dJobs] at hj
      obtain ⟨i, hi, h⟩ := termJobs_tgt tgt _ ds j hj; exact ⟨i, by simp; omega, h⟩
  | pre, ds, [] => by simp [dJobs]

theorem eJobs_tgt (tgt : ℕ → Fin n) : ∀ (pre : List (Fin n × Bool)) (rws ws : List (Fin n)),
    ∀ j ∈ eJobs tgt pre rws ws, ∃ i, i < rws.length + ws.length ∧ j.2 = tgt (i + 1)
  | pre, rf :: rd :: rrest, ws => by
      intro j hj
      rw [eJobs, List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨i, hi, h⟩ := dJobs_tgt _ _ _ ws j hj; exact ⟨i, by simp at hi ⊢; omega, h⟩
      · obtain ⟨i, hi, h⟩ := eJobs_tgt _ _ rrest ws j hj; exact ⟨i + 2, by simp; omega, h⟩
  | pre, [rf], ws => by
      intro j hj; rw [eJobs] at hj
      obtain ⟨i, hi, h⟩ := dJobs_tgt _ _ _ ws j hj; exact ⟨i, by simp at hi ⊢; omega, h⟩
  | pre, [], ws => by simp [eJobs]

theorem eff_eJobs (tgt : ℕ → Fin n) (M : ℕ) (htgt : InjBelow tgt M) (z : Qubits n)
    (ws : List (Fin n)) :
    ∀ (u : Bits) (pre : List (Fin n × Bool)) (rws : List (Fin n)) (rest : Bits) (i : ℕ),
      i < M → rws.length + 1 + ws.length ≤ M →
      patOK pre z = true → rws.map z = packOne u ++ rest →
      eff (eJobs tgt pre rws ws) z (tgt i) =
        (decide (2 * u.length + 1 ≤ i) && dOut (ws.map z) (i - (2 * u.length + 1)))
  | [], pre, rf :: rrest, rest, i, hi, hM, hpre, hr => by
      simp only [List.map_cons, packOne_nil, List.singleton_append, List.cons.injEq] at hr
      simp only [List.length_cons] at hM
      have hfirst : eff (dJobs (fun i => tgt (i + 1)) (pre ++ [(rf, false)]) [] ws) z (tgt i) =
            (decide (1 ≤ i) && dOut (ws.map z) (i - 1)) := by
        rcases i with _ | i
        · rw [eff_notarget]
          · simp
          · intro j hj; obtain ⟨k, hk, hk'⟩ := dJobs_tgt _ _ _ ws j hj
            rw [hk']; intro h; have := htgt _ _ (by simp at hk; omega) hi h; omega
        · have := eff_dJobs (fun i => tgt (i + 1)) (M - 1) (htgt.shift 1) z i (by omega)
            (pre ++ [(rf, false)]) [] ws (by simp; omega)
            (by simp [patOK_append, hpre, patOK_single, hr.1])
          rw [this]; simp [dOut]
      rcases rrest with _ | ⟨rd, rrest⟩
      · rw [eJobs, hfirst]; simp
      · rw [eJobs, eff_append, hfirst, eff_prefix_false _ z _ (pre ++ [(rf, true)])
          (by simp [patOK_append, patOK_single, hr.1]) (eJobs_prefix _ _ rrest ws)]
        simp
  | [], pre, [], rest, i, hi, hM, hpre, hr => by simp [packOne] at hr
  | b :: u, pre, rf :: rd :: rrest, rest, i, hi, hM, hpre, hr => by
      simp only [List.map_cons, packOne_cons, List.cons_append, List.cons.injEq] at hr
      simp only [List.length_cons] at hM
      obtain ⟨h1, h2, h3⟩ := hr
      rw [eJobs, eff_append, eff_prefix_false _ z _ (pre ++ [(rf, false)])
          (by simp [patOK_append, patOK_single, h1]) (dJobs_prefix _ _ _ ws)]
      have hne : ∀ j ∈ eJobs (fun i => tgt (i + 2)) (pre ++ [(rf, true)]) rrest ws, ∀ i', i' < 2 →
          j.2 ≠ tgt i' := by
        intro j hj i' hi' h
        obtain ⟨k, hk, hk'⟩ := eJobs_tgt _ _ rrest ws j hj
        rw [hk'] at h
        have := htgt _ _ (by omega) (by omega) h; omega
      rcases i with _ | _ | i
      · rw [eff_notarget _ _ _ (fun j hj => hne j hj 0 (by omega))]; simp
      · rw [eff_notarget _ _ _ (fun j hj => hne j hj 1 (by omega))]; simp
      · have := eff_eJobs (fun i => tgt (i + 2)) (M - 2) (htgt.shift 2) z ws
          u (pre ++ [(rf, true)]) rrest rest i (by omega) (by omega)
          (by simp [patOK_append, hpre, patOK_single, h1]) h3
        rw [this]
        simp only [List.length_cons, Bool.false_xor]
        have e1 : (2 * (u.length + 1) + 1 ≤ i + 2) ↔ (2 * u.length + 1 ≤ i) := by omega
        have e2 : i + 2 - (2 * (u.length + 1) + 1) = i - (2 * u.length + 1) := by omega
        simp only [e1, e2]
  | b :: u, pre, [rf], rest, i, hi, hM, hpre, hr => by
      simp [packOne] at hr
  | b :: u, pre, [], rest, i, hi, hM, hpre, hr => by simp [packOne] at hr

def copyJobs (tgt : ℕ → Fin n) : List (Fin n) → List (Job n)
  | [] => []
  | r :: rs => ([(r, true)], tgt 0) :: copyJobs (fun i => tgt (i + 1)) rs

theorem copyJobs_tgt (tgt : ℕ → Fin n) (rws : List (Fin n)) :
    ∀ j ∈ copyJobs tgt rws, ∃ k, k < rws.length ∧ j.2 = tgt k := by
  induction rws generalizing tgt with
  | nil => simp [copyJobs]
  | cons r rs ih =>
    intro j hj; simp only [copyJobs, List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨k, hk, hk'⟩ := ih _ j hj; exact ⟨k + 1, by simp; omega, hk'⟩

theorem eff_copyJobs (tgt : ℕ → Fin n) (M : ℕ) (htgt : InjBelow tgt M) (z : Qubits n) :
    ∀ (rws : List (Fin n)) (i : ℕ), rws.length ≤ M → i < M →
      eff (copyJobs tgt rws) z (tgt i) = (rws.map z).getD i false
  | [], i, _, _ => by simp [copyJobs, eff]
  | r :: rs, i, hM, hi => by
      simp only [List.length_cons] at hM
      rw [copyJobs, eff_cons]
      rcases i with _ | i
      · rw [eff_notarget]
        · simp [patOK_single]
        · intro j hj
          obtain ⟨k, hk, hk'⟩ := copyJobs_tgt _ rs j hj
          rw [hk']; intro h; have := htgt _ _ (by omega) hi h; omega
      · have := eff_copyJobs (fun i => tgt (i + 1)) (M - 1) (htgt.shift 1) z rs i (by omega) (by omega)
        rw [this]
        have e0 : tgt 0 ≠ tgt (i + 1) := fun h => by have := htgt _ _ (by omega) hi h; omega
        simp [e0]

end Encode

section Core
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def nv (B : Matrix ι Unit ℂ) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => B i ()) : EuclideanSpace ℂ ι)‖

theorem nv_eq (B : Matrix ι Unit ℂ) : nv B = √(∑ i, ‖B i ()‖ ^ 2) := by
  rw [nv, EuclideanSpace.norm_eq]

theorem nv_nonneg (B : Matrix ι Unit ℂ) : 0 ≤ nv B := norm_nonneg _

theorem nv_sq (B : Matrix ι Unit ℂ) : nv B ^ 2 = ∑ i, ‖B i ()‖ ^ 2 := by
  rw [nv_eq, Real.sq_sqrt (by positivity)]

theorem nv_sq_trace (B : Matrix ι Unit ℂ) : nv B ^ 2 = (Bᴴ * B).trace.re := by
  rw [nv_sq, trace_unit_self, Complex.ofReal_re]

theorem nv_add (A B : Matrix ι Unit ℂ) : nv (A + B) ≤ nv A + nv B := by
  unfold nv
  have : (WithLp.toLp 2 (fun i => (A + B) i ()) : EuclideanSpace ℂ ι) =
      WithLp.toLp 2 (fun i => A i ()) + WithLp.toLp 2 (fun i => B i ()) := by
    rw [← WithLp.toLp_add]; rfl
  rw [this]; exact norm_add_le _ _

theorem nv_unitary (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (B : Matrix ι Unit ℂ) :
    nv (U * B) = nv B := by
  have h : nv (U * B) ^ 2 = nv B ^ 2 := by
    rw [nv_sq_trace, nv_sq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ,
      hU, Matrix.one_mul]
  exact (pow_left_inj₀ (nv_nonneg _) (nv_nonneg _) (by norm_num : (2:ℕ) ≠ 0)).1 h

/-- The diagonal 0/1 matrix of a predicate. -/
noncomputable def dg (q : ι → Bool) : Matrix ι ι ℂ := Matrix.diagonal fun z => if q z then 1 else 0

theorem dg_apply_vec (q : ι → Bool) (B : Matrix ι Unit ℂ) (i : ι) :
    (dg q * B) i () = if q i then B i () else 0 := by
  simp [dg, Matrix.diagonal_mul]

theorem nv_dg_sq (q : ι → Bool) (B : Matrix ι Unit ℂ) :
    nv (dg q * B) ^ 2 = ∑ i, if q i then ‖B i ()‖ ^ 2 else 0 := by
  rw [nv_sq]; congr 1; funext i; rw [dg_apply_vec]; split_ifs <;> simp

theorem nv_dg_le (q : ι → Bool) (B : Matrix ι Unit ℂ) : nv (dg q * B) ≤ nv B := by
  have h : nv (dg q * B) ^ 2 ≤ nv B ^ 2 := by
    rw [nv_dg_sq, nv_sq]
    apply Finset.sum_le_sum; intro i _; split_ifs
    · exact le_refl _
    · positivity
  exact (pow_le_pow_iff_left₀ (nv_nonneg _) (nv_nonneg _) (by norm_num)).1 h

theorem nv_dg_pyth (q : ι → Bool) (B : Matrix ι Unit ℂ) :
    nv (dg q * B) ^ 2 + nv (dg (fun i => !q i) * B) ^ 2 = nv B ^ 2 := by
  rw [nv_dg_sq, nv_dg_sq, nv_sq, ← Finset.sum_add_distrib]
  congr 1; funext i; cases q i <;> simp

theorem dg_add_not (q : ι → Bool) : dg q + dg (fun i => !q i) = 1 := by
  ext i j
  simp only [dg, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> cases q i <;> simp_all

/-- The per-branch inequality: `p₀ + p₁ - w ≤ 2 √q √w`. -/
theorem core_ineq (φ : Matrix ι Unit ℂ) (W : Matrix ι ι ℂ) (hW : Wᴴ * W = 1) (q0 q1 : ι → Bool) :
    nv (dg q0 * φ) ^ 2 + nv (dg q1 * (W * φ)) ^ 2 - nv φ ^ 2 ≤
      2 * nv (dg q1 * (W * (dg q0 * φ))) * nv φ := by
  set a := nv (dg q1 * (W * (dg q0 * φ)))
  set b := nv (dg (fun i => !q0 i) * φ)
  set P0 := nv (dg q0 * φ)
  set P1 := nv (dg q1 * (W * φ))
  set w := nv φ
  have hsplit : dg q1 * (W * φ) = dg q1 * (W * (dg q0 * φ)) +
      dg q1 * (W * (dg (fun i => !q0 i) * φ)) := by
    rw [← Matrix.mul_add, ← Matrix.mul_add, ← Matrix.add_mul, dg_add_not, Matrix.one_mul]
  have h1 : P1 ≤ a + b := by
    have := nv_add (dg q1 * (W * (dg q0 * φ))) (dg q1 * (W * (dg (fun i => !q0 i) * φ)))
    rw [← hsplit] at this
    have h2 := nv_dg_le q1 (W * (dg (fun i => !q0 i) * φ))
    rw [nv_unitary W hW] at h2
    linarith
  have hpy : P0 ^ 2 + b ^ 2 = w ^ 2 := nv_dg_pyth q0 φ
  have hP1w : P1 ≤ w := by
    have := nv_dg_le q1 (W * φ); rw [nv_unitary W hW] at this; exact this
  have hbw : b ≤ w := nv_dg_le _ φ
  have ha : 0 ≤ a := nv_nonneg _
  have hb : 0 ≤ b := nv_nonneg _
  have hP1 : 0 ≤ P1 := nv_nonneg _
  have hw : 0 ≤ w := nv_nonneg _
  by_cases hc : P1 ≤ b
  · nlinarith
  · push_neg at hc
    nlinarith [mul_le_mul (show P1 - b ≤ a by linarith) (show P1 + b ≤ 2 * w by linarith)
      (by linarith) ha]

end Core

section SumSide

theorem nv_sq_outer {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι Unit ℂ) :
    (B * Bᴴ).trace.re = nv B ^ 2 := by
  rw [Matrix.trace_mul_comm, nv_sq_trace]

/-- Measuring the output wires and accepting by a predicate of the outcome. -/
theorem meas_pred {N : ℕ} (s : RoundStep N) (m : Bits) (B : Matrix (Qubits N) Unit ℂ)
    (f : Bits → Bool) :
    (∑ x : Qubits s.outW.length,
        if f (List.ofFn x) = true then (stepDM s m (List.ofFn x) (B * Bᴴ)).trace.re else 0) =
      nv (dg (fun z => f (readWires s.outW z)) * (s.op m * B)) ^ 2 := by
  set Y := s.op m * B
  have h1 : ∀ x : Qubits s.outW.length, (stepDM s m (List.ofFn x) (B * Bᴴ)).trace.re =
      ∑ z, if readWires s.outW z = List.ofFn x then ‖Y z ()‖ ^ 2 else 0 := by
    intro x
    rw [stepDM_pure, nv_sq_outer, nv_sq]
    congr 1; funext z
    simp only [outcomeProj, diagProj, Matrix.mul_assoc]
    rw [Matrix.diagonal_mul]
    split_ifs <;> simp [Y]
  simp_rw [h1]
  rw [nv_dg_sq]
  have h2 : ∀ x : Qubits s.outW.length,
      (if f (List.ofFn x) = true then
        ∑ z, (if readWires s.outW z = List.ofFn x then ‖Y z ()‖ ^ 2 else 0) else 0) =
      ∑ z, if readWires s.outW z = List.ofFn x then
        (if f (readWires s.outW z) = true then ‖Y z ()‖ ^ 2 else 0) else 0 := by
    intro x
    by_cases hf : f (List.ofFn x) = true
    · rw [if_pos hf]
      apply Finset.sum_congr rfl; intro z _
      by_cases hz : readWires s.outW z = List.ofFn x
      · rw [if_pos hz, if_pos hz, if_pos (hz ▸ hf)]
      · rw [if_neg hz, if_neg hz]
    · rw [if_neg hf]; symm
      apply Finset.sum_eq_zero; intro z _
      by_cases hz : readWires s.outW z = List.ofFn x
      · rw [if_pos hz, if_neg (by rw [hz]; exact hf)]
      · rw [if_neg hz]
  simp_rw [h2]
  rw [Finset.sum_comm]
  congr 1; funext z
  rw [Finset.sum_eq_single (fun j => z (s.outW.get j))]
  · have hr : readWires s.outW z = List.ofFn (fun j => z (s.outW.get j)) :=
      (readWires_eq_ofFn_iff _ _ _).2 rfl
    rw [← hr]; simp only [if_true]
  · intro x _ hx
    have : readWires s.outW z ≠ List.ofFn x := fun h => hx ((readWires_eq_ofFn_iff _ _ _).1 h).symm
    simp [this]
  · simp

theorem runFrom_msg_congr (S : QStrategy) (msg msg' : List Bits → Bits) (K : ℕ)
    (hmsg : ∀ d : List Bits, d.length < K → msg' d = msg d) :
    ∀ (os done : List Bits) (ρ : Matrix (Qubits S.N) (Qubits S.N) ℂ),
      done.length + os.length ≤ K → S.runFrom msg' done os ρ = S.runFrom msg done os ρ := by
  intro os
  induction os with
  | nil => intro done ρ _; rfl
  | cons o rest ih =>
    intro done ρ hlen
    simp only [QStrategy.runFrom]
    rw [hmsg done (by simp at hlen; omega)]
    exact ih _ _ (by simp at hlen ⊢; omega)

end SumSide

section SumBound
variable (Cm : CommitmentScheme) (S : QStrategy) (n : ℕ)

noncomputable def pureOf (S : QStrategy) (msg : List Bits → Bits) (os : List Bits) :
    Matrix (Qubits S.N) Unit ℂ := Classical.choose (run_pure S msg os)

theorem pureOf_spec (S : QStrategy) (msg : List Bits → Bits) (os : List Bits) :
    S.run msg (zeroDM S.inQ) os = pureOf S msg os * (pureOf S msg os)ᴴ :=
  Classical.choose_spec (run_pure S msg os)

def qb (b : Bool) (c : CoinSpace (Cm.receiver.coins (Cm.setup n))) (os : List Bits) :
    Qubits S.N → Bool := fun z =>
  Cm.ropen [b] (decodeOne (readWires (S.stepAt (Cm.rounds n)).outW z)) (commTranscript Cm n c os)
    (encCoins c) (Cm.setup n)

noncomputable def Wop : Matrix (Qubits S.N) (Qubits S.N) ℂ :=
  (S.stepAt (Cm.rounds n)).op [true] * ((S.stepAt (Cm.rounds n)).op [false])ᴴ

noncomputable def qval (c : CoinSpace (Cm.receiver.coins (Cm.setup n))) (os : List Bits) : ℝ :=
  nv (dg (qb Cm S n true c os) * (Wop Cm S n * (dg (qb Cm S n false c os) *
    ((S.stepAt (Cm.rounds n)).op [false] * pureOf S (expMsg Cm n c fun _ => []) os)))) ^ 2

/-- The summand of the sum-binding experiment. -/
noncomputable def sbTerm (b : Bool) (c : CoinSpace (Cm.receiver.coins (Cm.setup n)))
    (os : List Bits) : ℝ :=
  if Cm.ropen [b] (decodeOne (os.getD (Cm.rounds n) [])) (commTranscript Cm n c (os.take (Cm.rounds n)))
      (encCoins c) (Cm.setup n) = true then
    (S.run (expMsg Cm n c (fun _ => [b])) (zeroDM S.inQ) os).trace.re
  else 0

theorem sumBinding_eq : sumBindingProb Cm S n =
    avgOver Bool fun b => avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
      ∑ o : S.Outs (Cm.rounds n + 1), sbTerm Cm S n b c (QStrategy.outList o) := rfl

theorem outList_length {K : ℕ} (o : S.Outs K) : (QStrategy.outList o).length = K := by
  simp [QStrategy.outList]

theorem sbTerm_branch (b : Bool) (c : CoinSpace (Cm.receiver.coins (Cm.setup n)))
    (o : S.Outs (Cm.rounds n)) :
    (∑ x : Qubits (S.stepAt (Cm.rounds n)).outW.length,
        sbTerm Cm S n b c (QStrategy.outList o ++ [List.ofFn x])) =
      nv (dg (qb Cm S n b c (QStrategy.outList o)) * ((S.stepAt (Cm.rounds n)).op [b] *
        pureOf S (expMsg Cm n c fun _ => []) (QStrategy.outList o))) ^ 2 := by
  set os := QStrategy.outList o
  have hlen : os.length = Cm.rounds n := outList_length S o
  have hrun : ∀ y : Bits, S.run (expMsg Cm n c (fun _ => [b])) (zeroDM S.inQ) (os ++ [y]) =
      stepDM (S.stepAt (Cm.rounds n)) [b] y
        (pureOf S (expMsg Cm n c fun _ => []) os * (pureOf S (expMsg Cm n c fun _ => []) os)ᴴ) := by
    intro y
    rw [← pureOf_spec, QStrategy.run, QStrategy.run, runFrom_snoc]
    simp only [List.nil_append, hlen]
    have hm : expMsg Cm n c (fun _ => [b]) os = [b] := by
      simp [expMsg, hlen]
    rw [hm, runFrom_msg_congr S (expMsg Cm n c fun _ => []) (expMsg Cm n c fun _ => [b])
      (Cm.rounds n) (fun d hd => by simp [expMsg, hd]) os [] _ (by simp [hlen])]
  refine Eq.trans ?_ (meas_pred (S.stepAt (Cm.rounds n)) [b]
    (pureOf S (expMsg Cm n c fun _ => []) os)
    (fun s => Cm.ropen [b] (decodeOne s) (commTranscript Cm n c os) (encCoins c) (Cm.setup n)))
  apply Finset.sum_congr rfl
  intro x _
  have ht : ∀ y : Bits, (os ++ [y]).take (Cm.rounds n) = os := by
    intro y; rw [← hlen]; simp
  have hg : ∀ y : Bits, (os ++ [y]).getD (Cm.rounds n) [] = y := by
    intro y; rw [← hlen]; simp
  rw [sbTerm, ht, hg, hrun]

end SumBound

section SumBound2
variable (Cm : CommitmentScheme) (S : QStrategy) (n : ℕ)

theorem Wop_unitary : (Wop Cm S n)ᴴ * Wop Cm S n = 1 := by
  rw [Wop, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc ((S.stepAt (Cm.rounds n)).op [true])ᴴ, op_unitary, Matrix.one_mul,
    op_unitary']

theorem Wop_mul (B : Matrix (Qubits S.N) Unit ℂ) :
    Wop Cm S n * ((S.stepAt (Cm.rounds n)).op [false] * B) = (S.stepAt (Cm.rounds n)).op [true] * B := by
  rw [Wop, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ B, op_unitary, Matrix.one_mul]

theorem branch_ineq (c : CoinSpace (Cm.receiver.coins (Cm.setup n))) (os : List Bits) :
    nv (dg (qb Cm S n false c os) * ((S.stepAt (Cm.rounds n)).op [false] *
        pureOf S (expMsg Cm n c fun _ => []) os)) ^ 2 +
      nv (dg (qb Cm S n true c os) * ((S.stepAt (Cm.rounds n)).op [true] *
        pureOf S (expMsg Cm n c fun _ => []) os)) ^ 2 -
      nv (pureOf S (expMsg Cm n c fun _ => []) os) ^ 2 ≤
    2 * (√(qval Cm S n c os) * √(nv (pureOf S (expMsg Cm n c fun _ => []) os) ^ 2)) := by
  set B := pureOf S (expMsg Cm n c fun _ => []) os
  have h := core_ineq ((S.stepAt (Cm.rounds n)).op [false] * B) (Wop Cm S n) (Wop_unitary Cm S n)
    (qb Cm S n false c os) (qb Cm S n true c os)
  rw [Wop_mul, nv_unitary _ (op_unitary _ _)] at h
  rw [qval, Real.sqrt_sq (nv_nonneg _), Real.sqrt_sq (nv_nonneg _)]
  linarith

theorem sum_w (hV : S.Valid) (c : CoinSpace (Cm.receiver.coins (Cm.setup n))) :
    (∑ o : S.Outs (Cm.rounds n),
      nv (pureOf S (expMsg Cm n c fun _ => []) (QStrategy.outList o)) ^ 2) = 1 := by
  have h := sum_run_trace S (expMsg Cm n c fun _ => []) (zeroDM S.inQ) (Cm.rounds n)
  rw [initDM_zero_trace S hV] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simp only [Complex.one_re] at h2
  rw [← h2]
  apply Finset.sum_congr rfl; intro o _
  rw [pureOf_spec, nv_sq_outer]

theorem sum_bound (hV : S.Valid) :
    sumBindingProb Cm S n - 1 / 2 ≤
      √(avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
        ∑ o : S.Outs (Cm.rounds n), qval Cm S n c (QStrategy.outList o)) := by
  set C := CoinSpace (Cm.receiver.coins (Cm.setup n))
  set O := S.Outs (Cm.rounds n)
  set B : C → O → Matrix (Qubits S.N) Unit ℂ := fun c o =>
    pureOf S (expMsg Cm n c fun _ => []) (QStrategy.outList o)
  set P : Bool → C → O → ℝ := fun b c o =>
    nv (dg (qb Cm S n b c (QStrategy.outList o)) * ((S.stepAt (Cm.rounds n)).op [b] * B c o)) ^ 2
  set w : C → O → ℝ := fun c o => nv (B c o) ^ 2
  set q : C → O → ℝ := fun c o => qval Cm S n c (QStrategy.outList o)
  have hsb : sumBindingProb Cm S n = avgOver Bool fun b => avgOver C fun c => ∑ o : O, P b c o := by
    rw [sumBinding_eq]
    congr 1; funext b; congr 1; funext c
    rw [sum_outs_succ S (Cm.rounds n) (sbTerm Cm S n b c)]
    apply Finset.sum_congr rfl; intro o _
    exact sbTerm_branch Cm S n b c o
  have hbr : ∀ c o, P false c o + P true c o - w c o ≤ 2 * (√(q c o) * √(w c o)) :=
    fun c o => branch_ineq Cm S n c (QStrategy.outList o)
  have hw1 : ∀ c, ∑ o : O, w c o = 1 := fun c => sum_w Cm S n hV c
  have hq0 : ∀ c o, 0 ≤ q c o := fun c o => by simp only [q, qval]; positivity
  have hw0 : ∀ c o, 0 ≤ w c o := fun c o => by simp only [w]; positivity
  set k : ℝ := (Fintype.card C : ℝ)
  have hk0 : 0 ≤ k := by positivity
  have hcs : ∑ c : C, ∑ o : O, √(q c o) * √(w c o) ≤
      √(∑ c : C, ∑ o : O, q c o) * √(∑ c : C, ∑ o : O, w c o) := by
    have := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (C × O))
      (f := fun p => q p.1 p.2) (g := fun p => w p.1 p.2) (fun p => hq0 _ _) (fun p => hw0 _ _)
    simpa only [Fintype.sum_prod_type] using this
  have hsw : ∑ c : C, ∑ o : O, w c o = k := by
    simp only [hw1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, k]
  rw [hsw] at hcs
  rw [hsb]
  have e1 : (avgOver Bool fun b => avgOver C fun c => ∑ o : O, P b c o) =
      (k⁻¹ * (∑ c : C, ∑ o : O, P false c o) + k⁻¹ * (∑ c : C, ∑ o : O, P true c o)) / 2 := by
    simp only [avgOver, Fintype.card_bool, Fintype.sum_bool, smul_eq_mul, k]; push_cast; ring
  have e2 : (avgOver C fun c => ∑ o : O, qval Cm S n c (QStrategy.outList o)) =
      k⁻¹ * ∑ c : C, ∑ o : O, q c o := by
    simp only [avgOver, smul_eq_mul]; rfl
  rw [e1, e2]
  rcases eq_or_lt_of_le hk0 with hk | hk
  · rw [← hk, inv_zero]; simp
  · have hsum : ∑ c : C, ∑ o : O, (P false c o + P true c o - w c o) ≤
        2 * (√(∑ c : C, ∑ o : O, q c o) * √k) := by
      calc _ ≤ ∑ c : C, ∑ o : O, 2 * (√(q c o) * √(w c o)) :=
            Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun o _ => hbr c o
        _ = 2 * ∑ c : C, ∑ o : O, √(q c o) * √(w c o) := by simp [Finset.mul_sum]
        _ ≤ _ := by linarith
    have hsplit : ∑ c : C, ∑ o : O, (P false c o + P true c o - w c o) =
        (∑ c : C, ∑ o : O, P false c o) + (∑ c : C, ∑ o : O, P true c o) - k := by
      rw [← hsw]; simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rw [hsplit] at hsum
    have hsq : √(k⁻¹ * ∑ c : C, ∑ o : O, q c o) = √(∑ c : C, ∑ o : O, q c o) / √k := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_inv]; ring
    have hsk : √k * √k = k := Real.mul_self_sqrt hk0
    have hskp : 0 < √k := Real.sqrt_pos.2 hk
    have e3 : (k⁻¹ * (∑ c : C, ∑ o : O, P false c o) + k⁻¹ * (∑ c : C, ∑ o : O, P true c o)) / 2
        - 1 / 2 = ((∑ c : C, ∑ o : O, P false c o) + (∑ c : C, ∑ o : O, P true c o) - k) / (2 * k) := by
      field_simp
    rw [e3, hsq, div_le_div_iff₀ (by positivity) hskp]
    have := mul_le_mul_of_nonneg_right hsum hskp.le
    have h5 : 2 * (√(∑ c : C, ∑ o : O, q c o) * √k) * √k = √(∑ c : C, ∑ o : O, q c o) * (2 * k) := by
      linear_combination (2 * √(∑ c : C, ∑ o : O, q c o)) * hsk
    linarith

end SumBound2

section Ctrl
variable {n : ℕ}

theorem nodup_of_perm_sub {l l' L : List (Fin n)} (hp : l.Perm l') (hs : l'.Sublist L) (h : L.Nodup) :
    l.Nodup := (hp.nodup_iff).2 (h.sublist hs)

theorem termJobs_ctrl (tgt : ℕ → Fin n) (P : List (Fin n × Bool)) (ds : List (Fin n))
    (hnd : (P.map Prod.fst ++ ds).Nodup) :
    ∀ j ∈ termJobs tgt P ds, (j.1.map Prod.fst).Nodup ∧
      (∀ c ∈ j.1, c.1 ∈ P.map Prod.fst ++ ds) ∧ j.1.length ≤ P.length + 1 := by
  induction ds generalizing tgt with
  | nil => simp [termJobs]
  | cons d ds ih =>
    intro j hj
    simp only [termJobs, List.mem_cons] at hj
    have hP : (P.map Prod.fst).Nodup := hnd.sublist (List.sublist_append_left _ _)
    rcases hj with rfl | rfl | hj
    · refine ⟨hP, fun c hc => List.mem_append_left _ (List.mem_map_of_mem hc), by simp⟩
    · refine ⟨?_, ?_, by simp⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        exact hnd.sublist (List.Sublist.append_left (List.Sublist.cons_cons _ (List.nil_sublist _)) _)
      · intro c hc
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with hc | rfl
        · exact List.mem_append_left _ (List.mem_map_of_mem hc)
        · simp
    · have hnd' : (P.map Prod.fst ++ ds).Nodup :=
        hnd.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
      obtain ⟨h1, h2, h3⟩ := ih _ hnd' j hj
      refine ⟨h1, fun c hc => ?_, h3⟩
      have := h2 c hc
      simp only [List.mem_append, List.mem_cons] at this ⊢
      tauto

theorem dJobs_ctrl (tgt : ℕ → Fin n) : ∀ (pre : List (Fin n × Bool)) (ds ws : List (Fin n)),
    (pre.map Prod.fst ++ ds ++ ws).Nodup →
    ∀ j ∈ dJobs tgt pre ds ws, (j.1.map Prod.fst).Nodup ∧
      (∀ c ∈ j.1, c.1 ∈ pre.map Prod.fst ++ ds ++ ws) ∧ j.1.length ≤ pre.length + ws.length + 1
  | pre, ds, f :: d :: rest, hnd => by
      intro j hj
      rw [dJobs, List.mem_append] at hj
      rcases hj with hj | hj
      · have hnd' : ((pre ++ [(f, false)]).map Prod.fst ++ ds).Nodup := by
          refine nodup_of_perm_sub (l' := pre.map Prod.fst ++ ds ++ [f]) ?_ ?_ hnd
          · simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
            exact List.Perm.append_left _ List.perm_append_comm
          · exact List.Sublist.append_left (List.Sublist.cons_cons _ (List.nil_sublist _)) _
        obtain ⟨h1, h2, h3⟩ := termJobs_ctrl tgt _ ds hnd' j hj
        refine ⟨h1, fun c hc => ?_, by simp at h3 ⊢; omega⟩
        have := h2 c hc
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
          List.mem_nil_iff, or_false] at this ⊢
        tauto
      · have hnd' : ((pre ++ [(f, true)]).map Prod.fst ++ (ds ++ [d]) ++ rest).Nodup := by
          refine nodup_of_perm_sub (l' := pre.map Prod.fst ++ ds ++ f :: d :: rest) ?_
            (List.Sublist.refl _) hnd
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append, List.cons_append]
          refine List.Perm.append_left _ ?_
          rw [List.perm_iff_count]; intro a
          simp only [List.count_append, List.count_cons, List.count_nil]
          omega
        obtain ⟨h1, h2, h3⟩ := dJobs_ctrl tgt _ _ rest hnd' j hj
        refine ⟨h1, fun c hc => ?_, by simp at h3 ⊢; omega⟩
        have := h2 c hc
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
          List.mem_nil_iff, or_false] at this ⊢
        tauto
  | pre, ds, [f], hnd => by
      intro j hj
      rw [dJobs] at hj
      have hnd' : ((pre ++ [(f, false)]).map Prod.fst ++ ds).Nodup := by
        refine nodup_of_perm_sub (l' := pre.map Prod.fst ++ ds ++ [f]) ?_ (List.Sublist.refl _) hnd
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
        exact List.Perm.append_left _ List.perm_append_comm
      obtain ⟨h1, h2, h3⟩ := termJobs_ctrl tgt _ ds hnd' j hj
      refine ⟨h1, fun c hc => ?_, by simp at h3 ⊢; omega⟩
      have := h2 c hc
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.mem_nil_iff, or_false] at this ⊢
      tauto
  | pre, ds, [], _ => by simp [dJobs]

theorem eJobs_ctrl (tgt : ℕ → Fin n) : ∀ (pre : List (Fin n × Bool)) (rws ws : List (Fin n)),
    (pre.map Prod.fst ++ rws ++ ws).Nodup →
    ∀ j ∈ eJobs tgt pre rws ws, (j.1.map Prod.fst).Nodup ∧
      (∀ c ∈ j.1, c.1 ∈ pre.map Prod.fst ++ rws ++ ws) ∧
        j.1.length ≤ pre.length + rws.length + ws.length + 2
  | pre, rf :: rd :: rrest, ws, hnd => by
      intro j hj
      rw [eJobs, List.mem_append] at hj
      rcases hj with hj | hj
      · have hnd' : ((pre ++ [(rf, false)]).map Prod.fst ++ [] ++ ws).Nodup := by
          refine nodup_of_perm_sub (l' := pre.map Prod.fst ++ [rf] ++ ws) (by simp) ?_ hnd
          simp only [List.append_assoc]
          exact List.Sublist.append_left (List.Sublist.cons_cons rf
            (List.sublist_append_right (rd :: rrest) ws)) _
        obtain ⟨h1, h2, h3⟩ := dJobs_ctrl _ _ [] ws hnd' j hj
        refine ⟨h1, fun c hc => ?_, by simp at h3 ⊢; omega⟩
        have := h2 c hc
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
          List.mem_nil_iff, or_false, List.append_nil] at this ⊢
        tauto
      · have hnd' : ((pre ++ [(rf, true)]).map Prod.fst ++ rrest ++ ws).Nodup := by
          refine nodup_of_perm_sub (l' := pre.map Prod.fst ++ [rf] ++ rrest ++ ws) (by simp) ?_ hnd
          simp only [List.append_assoc, List.singleton_append]
          exact List.Sublist.append_left (List.Sublist.cons_cons rf
            ((List.sublist_cons_self rd rrest).append_right ws)) _
        obtain ⟨h1, h2, h3⟩ := eJobs_ctrl _ _ rrest ws hnd' j hj
        refine ⟨h1, fun c hc => ?_, by simp at h3 ⊢; omega⟩
        have := h2 c hc
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
          List.mem_nil_iff, or_false] at this ⊢
        tauto
  | pre, [rf], ws, hnd => by
      intro j hj
      rw [eJobs] at hj
      have hnd' : ((pre ++ [(rf, false)]).map Prod.fst ++ [] ++ ws).Nodup := by simpa using hnd
      obtain ⟨h1, h2, h3⟩ := dJobs_ctrl _ _ [] ws hnd' j hj
      refine ⟨h1, fun c hc => ?_, by simp at h3 ⊢; omega⟩
      have := h2 c hc
      simpa using this
  | pre, [], ws, _ => by simp [eJobs]

theorem copyJobs_ctrl (tgt : ℕ → Fin n) (rws : List (Fin n)) :
    ∀ j ∈ copyJobs tgt rws, ∃ r ∈ rws, j.1 = [(r, true)] := by
  induction rws generalizing tgt with
  | nil => simp [copyJobs]
  | cons r rs ih =>
    intro j hj; simp only [copyJobs, List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact ⟨r, List.mem_cons_self, rfl⟩
    · obtain ⟨r', hr', h⟩ := ih _ j hj; exact ⟨r', List.mem_cons_of_mem _ hr', h⟩

end Ctrl

section Vec
variable {N m N' : ℕ} (h : N + m = N')

def jn (p : Qubits N) (q : Qubits m) : Qubits N' := (splitQ h).symm (p, q)

theorem jn_e (p : Qubits N) (q : Qubits m) : jn h p q ∘ eL h = p := split_symm_e h p q
theorem jn_f (p : Qubits N) (q : Qubits m) : jn h p q ∘ fL h = q := split_symm_f h p q
theorem jn_self (y : Qubits N') : jn h (y ∘ eL h) (y ∘ fL h) = y := (splitQ h).symm_apply_apply y

def tv (B : Matrix (Qubits N) Unit ℂ) (σ : Qubits m → ℂ) : Matrix (Qubits N') Unit ℂ :=
  Matrix.of fun y _ => B (y ∘ eL h) () * σ (y ∘ fL h)

def e0 : Qubits m → ℂ := fun q => if q = (fun _ => false) then 1 else 0

theorem tens_pure (B : Matrix (Qubits N) Unit ℂ) :
    tens h (B * Bᴴ) (zeroDM m) = tv h B e0 * (tv h B e0)ᴴ := by
  ext y z
  simp only [tens, tv, e0, zeroDM, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.univ_unique, Finset.sum_singleton, star_mul']
  split_ifs <;> simp_all <;> ring

theorem embedOp_vec (A : Matrix (Qubits N) (Qubits N) ℂ) (v : Matrix (Qubits N') Unit ℂ)
    (y : Qubits N') : (embedOp A (eL h) * v) y () =
      ∑ p : Qubits N, A (y ∘ eL h) p * v (jn h p (y ∘ fL h)) () := by
  rw [Matrix.mul_apply, sum_split h]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single (y ∘ fL h)]
  · simp only [embedOp, Matrix.of_apply]
    rw [if_pos ((offRange_iff h _ _).2 (by rw [split_symm_f])), split_symm_e]; rfl
  · intro q _ hq
    simp only [embedOp, Matrix.of_apply]
    rw [if_neg (fun H => hq (by rw [← split_symm_f h p q]; exact ((offRange_iff h _ _).1 H).symm))]
    simp
  · simp

theorem embedOp_tv (A : Matrix (Qubits N) (Qubits N) ℂ) (B : Matrix (Qubits N) Unit ℂ)
    (σ : Qubits m → ℂ) : embedOp A (eL h) * tv h B σ = tv h (A * B) σ := by
  ext y u
  rw [embedOp_vec]
  simp only [tv, Matrix.of_apply, jn_e, jn_f, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro p _; ring

/-- A permutation agreeing with an involution on the support of `v`. -/
theorem permOf_vec (F j : Qubits N' → Qubits N') (cl : Qubits N' → Prop)
    (hF : ∀ y, cl y → F y = j y) (hinv : ∀ y, j (j y) = y) (hcl : ∀ y, cl (j y) ↔ cl y)
    (v : Matrix (Qubits N') Unit ℂ) (hv : ∀ y, ¬ cl y → v y () = 0) (y : Qubits N') :
    (permOf F * v) y () = v (j y) () := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (j y)]
  · by_cases hc : cl (j y)
    · simp [permOf, hF _ hc, hinv]
    · simp [hv _ hc]
  · intro z _ hz
    by_cases hc : cl z
    · simp only [permOf, Matrix.of_apply]
      rw [if_neg]; · simp
      intro hy; apply hz; rw [hy, hF _ hc, hinv]
    · simp [hv _ hc]
  · simp

theorem nv_sq_ge_slice (v : Matrix (Qubits N') Unit ℂ) (q : Qubits m) :
    ∑ p : Qubits N, ‖v (jn h p q) ()‖ ^ 2 ≤ nv v ^ 2 := by
  rw [nv_sq, sum_split h]
  apply Finset.sum_le_sum; intro p _
  exact Finset.single_le_sum (f := fun q => ‖v ((splitQ h).symm (p, q)) ()‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ q)

/-- The abstract circuit bound. -/
theorem main_bound (U0 W : Matrix (Qubits N) (Qubits N) ℂ) (B : Matrix (Qubits N) Unit ℂ)
    (FD FE jD jE : Qubits N' → Qubits N') (clf : Qubits m → Prop)
    (q0 q1 : Qubits N → Bool) (g : Qubits N' → Bool) (fstar : Qubits m)
    (hD : ∀ y, clf (y ∘ fL h) → FD y = jD y) (hDinv : ∀ y, jD (jD y) = y)
    (hDcl : ∀ y, clf (jD y ∘ fL h) ↔ clf (y ∘ fL h)) (hDN : ∀ y, jD y ∘ eL h = y ∘ eL h)
    (hE : ∀ y, clf (y ∘ fL h) → FE y = jE y) (hEinv : ∀ y, jE (jE y) = y)
    (hEcl : ∀ y, clf (jE y ∘ fL h) ↔ clf (y ∘ fL h))
    (hcl0 : clf (fun _ => false))
    (hstar : ∀ p, (jD (jn h p fstar) ∘ fL h = fun _ => false) ↔ q0 p = true)
    (hg : ∀ p, q1 p = true → g (jE (jn h p fstar)) = true) :
    nv (dg q1 * (W * (dg q0 * (U0 * B)))) ^ 2 ≤
      nv (dg g * (permOf FE * (embedOp W (eL h) * (permOf FD * (embedOp U0 (eL h) *
        tv h B e0))))) ^ 2 := by
  rw [embedOp_tv]
  set v1 := tv h (U0 * B) e0
  have hv1 : ∀ y, ¬ clf (y ∘ fL h) → v1 y () = 0 := by
    intro y hy
    simp only [v1, tv, e0, Matrix.of_apply]
    rw [if_neg (fun h0 => hy (by rw [h0]; exact hcl0))]; simp
  set v2 := permOf FD * v1
  have hv2 : ∀ y, v2 y () = (U0 * B) (y ∘ eL h) () * e0 (jD y ∘ fL h) := by
    intro y
    show (permOf FD * v1) y () = _
    rw [permOf_vec FD jD (fun y => clf (y ∘ fL h)) hD hDinv hDcl v1 hv1 y]
    simp [v1, tv, hDN]
  set v3 := embedOp W (eL h) * v2
  have hv3 : ∀ y, ¬ clf (y ∘ fL h) → v3 y () = 0 := by
    intro y hy
    show (embedOp W (eL h) * v2) y () = 0
    rw [embedOp_vec]
    apply Finset.sum_eq_zero; intro p _
    rw [hv2]
    have : ¬ clf (jD (jn h p (y ∘ fL h)) ∘ fL h) := by rw [hDcl, jn_f]; exact hy
    simp only [e0]
    rw [if_neg (fun h0 => this (by rw [h0]; exact hcl0))]; simp
  have hv3star : ∀ p, v3 (jn h p fstar) () = (W * (dg q0 * (U0 * B))) p () := by
    intro p
    show (embedOp W (eL h) * v2) (jn h p fstar) () = _
    rw [embedOp_vec, jn_e, jn_f, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro p' _
    rw [hv2, jn_e, dg_apply_vec]
    congr 1
    simp only [e0]
    by_cases hq : q0 p' = true
    · rw [if_pos ((hstar p').2 hq), if_pos hq, mul_one]
    · rw [if_neg (fun h0 => hq ((hstar p').1 h0)), if_neg hq, mul_zero]
  set v4 := permOf FE * v3
  have hv4 : ∀ y, v4 y () = v3 (jE y) () :=
    permOf_vec FE jE (fun y => clf (y ∘ fL h)) hE hEinv hEcl v3 hv3
  rw [nv_dg_sq, nv_dg_sq]
  have hre : ∑ y : Qubits N', (if g y = true then ‖v4 y ()‖ ^ 2 else 0) =
      ∑ y : Qubits N', (if g (jE y) = true then ‖v3 y ()‖ ^ 2 else 0) := by
    let e : Qubits N' ≃ Qubits N' := ⟨jE, jE, hEinv, hEinv⟩
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl; intro y _
    simp only [e, Equiv.coe_fn_mk, hv4, hEinv]
  rw [hre]
  calc ∑ p : Qubits N, (if q1 p = true then ‖(W * (dg q0 * (U0 * B))) p ()‖ ^ 2 else 0)
      ≤ ∑ p : Qubits N, (if g (jE (jn h p fstar)) = true then ‖v3 (jn h p fstar) ()‖ ^ 2 else 0) := by
        apply Finset.sum_le_sum; intro p _
        by_cases hq : q1 p = true
        · rw [if_pos hq, if_pos (hg p hq), hv3star]
        · rw [if_neg hq]; split_ifs <;> positivity
    _ ≤ _ := by
        have := nv_sq_ge_slice h (dg (fun y => g (jE y)) * v3) fstar
        rw [nv_dg_sq] at this
        refine le_trans ?_ this
        apply le_of_eq; apply Finset.sum_congr rfl; intro p _
        rw [dg_apply_vec]; split_ifs <;> simp

end Vec

section Layout
variable {N N' : ℕ} (L : ℕ) (h : N + (5 * L + 7) = N')

def fw (i : ℕ) : Fin N' := fL h ⟨i % (5 * L + 7), Nat.mod_lt _ (by omega)⟩

theorem fw_val (i : ℕ) : (fw L h i).val = N + i % (5 * L + 7) := rfl

theorem fw_inj (a b : ℕ) (ha : a < 5 * L + 7) (hb : b < 5 * L + 7) (hab : fw L h a = fw L h b) :
    a = b := by
  have := congrArg Fin.val hab
  rw [fw_val, fw_val, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  omega

theorem fw_ne_eL (i : ℕ) (j : Fin N) : fw L h i ≠ eL h j := by
  intro hh; have := congrArg Fin.val hh; rw [fw_val, eL_val] at this; omega

theorem fw_eq_fL (j : Fin (5 * L + 7)) : fw L h j.val = fL h j := by
  apply Fin.ext; rw [fw_val, fL_val, Nat.mod_eq_of_lt j.isLt]

theorem injBelow_fw (off M : ℕ) (hM : off + M ≤ 5 * L + 7) :
    InjBelow (fun i => fw L h (off + i)) M := by
  intro a b ha hb hab
  have := fw_inj L h _ _ (by omega) (by omega) hab
  omega

def Rw (i : ℕ) : Fin N' := fw L h i
def Ow (i : ℕ) : Fin N' := fw L h (L + 1 + i)
def ancL : List (Fin N') := (List.range (2 * L + 4)).map fun i => fw L h (3 * L + 3 + i)
def rws : List (Fin N') := (List.range (L + 1)).map (Rw L h)
def ows : List (Fin N') := (List.range (2 * L + 2)).map (Ow L h)

theorem ancL_nodup : (ancL L h).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro a ha b hb hab
  simp at ha hb
  have := fw_inj L h _ _ (by omega) (by omega) hab; omega

theorem mem_ancL (a : Fin N') : a ∈ ancL L h ↔ ∃ i < 2 * L + 4, a = fw L h (3 * L + 3 + i) := by
  simp [ancL, eq_comm]

theorem rws_nodup : (rws L h).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro a ha b hb hab
  simp at ha hb
  exact fw_inj L h _ _ (by omega) (by omega) hab

variable (outW : List (Fin N))

def wsL : List (Fin N') := outW.map (eL h)

def jobsD : List (Job N') := dJobs (Rw L h) [] [] (wsL L h outW)

def jobsE : List (Job N') :=
  copyJobs (Ow L h) (rws L h) ++ eJobs (Ow L h) [] (rws L h) (wsL L h outW)

theorem wsL_nodup (hnd : outW.Nodup) : (wsL L h outW).Nodup :=
  hnd.map (eL h).injective

theorem jobsD_ctrl (hnd : outW.Nodup) (hL : outW.length = L) :
    ∀ j ∈ jobsD L h outW, (j.1.map Prod.fst).Nodup ∧ (∀ c ∈ j.1, ∃ i, c.1 = eL h i) ∧
      j.1.length ≤ L + 1 ∧ ∃ i < L, j.2 = fw L h i := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := dJobs_ctrl (Rw L h) [] [] (wsL L h outW) (by simpa using wsL_nodup L h outW hnd)
    j hj
  obtain ⟨i, hi, hi'⟩ := dJobs_tgt (Rw L h) [] [] (wsL L h outW) j hj
  refine ⟨h1, fun c hc => ?_, by simp [wsL, hL] at h3; omega, ⟨i, by simp [wsL, hL] at hi; omega, hi'⟩⟩
  have := h2 c hc
  simp [wsL] at this
  obtain ⟨a, _, ha⟩ := this
  exact ⟨a, ha.symm⟩

theorem jobsE_ctrl (hnd : outW.Nodup) (hL : outW.length = L) :
    ∀ j ∈ jobsE L h outW, (j.1.map Prod.fst).Nodup ∧
      (∀ c ∈ j.1, (∃ i, c.1 = eL h i) ∨ ∃ i < L + 1, c.1 = fw L h i) ∧
      j.1.length ≤ 2 * L + 3 ∧ ∃ i < 2 * L + 2, j.2 = fw L h (L + 1 + i) := by
  intro j hj
  rw [jobsE, List.mem_append] at hj
  rcases hj with hj | hj
  · obtain ⟨r, hr, h1⟩ := copyJobs_ctrl (Ow L h) (rws L h) j hj
    obtain ⟨k, hk, hk'⟩ := copyJobs_tgt (Ow L h) (rws L h) j hj
    simp only [rws, List.length_map, List.length_range] at hk
    refine ⟨by simp [h1], fun c hc => ?_, by simp [h1], ⟨k, by omega, hk'⟩⟩
    rw [h1] at hc; simp at hc; subst hc
    simp [rws, Rw] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    exact Or.inr ⟨a, by omega, rfl⟩
  · have hnd' : (([] : List (Fin N' × Bool)).map Prod.fst ++ rws L h ++ wsL L h outW).Nodup := by
      simp only [List.map_nil, List.nil_append]
      rw [List.nodup_append]
      refine ⟨rws_nodup L h, wsL_nodup L h outW hnd, ?_⟩
      intro a ha b hb hab
      simp [rws, Rw] at ha; simp [wsL] at hb
      obtain ⟨i, _, rfl⟩ := ha; obtain ⟨k, _, rfl⟩ := hb
      exact fw_ne_eL L h i k hab
    obtain ⟨h1, h2, h3⟩ := eJobs_ctrl (Ow L h) [] (rws L h) (wsL L h outW) hnd' j hj
    obtain ⟨i, hi, hi'⟩ := eJobs_tgt (Ow L h) [] (rws L h) (wsL L h outW) j hj
    simp only [rws, wsL, List.length_map, List.length_range, hL] at hi h3
    refine ⟨h1, fun c hc => ?_, by simp at h3; omega, ⟨i + 1, by omega, by rw [hi']; rfl⟩⟩
    have := h2 c hc
    simp [rws, wsL, Rw] at this
    rcases this with ⟨a, ha, h'⟩ | ⟨a, _, h'⟩
    · exact Or.inr ⟨a, by omega, h'.symm⟩
    · exact Or.inl ⟨a, h'.symm⟩

end Layout

/-- The ancillas are clean. -/
def clf (L : ℕ) (q : Qubits (5 * L + 7)) : Prop :=
  ∀ i (hi : i < 2 * L + 4), q ⟨3 * L + 3 + i, by omega⟩ = false

section Layout2
variable {N N' : ℕ} (L : ℕ) (h : N + (5 * L + 7) = N') (outW : List (Fin N))

theorem range_getD (l : Bits) (M : ℕ) (hl : l.length ≤ M) :
    (List.range M).map (fun i => l.getD i false) = l ++ List.replicate (M - l.length) false := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem_append]
    split_ifs with hi
    · simp [hi]
    · simp at h1; rw [List.getElem?_eq_none (by omega)]; simp

theorem decodeOne_len (w : Bits) : 2 * (decodeOne w).length + 1 ≤ w.length + 1 := by
  unfold decodeOne unpack
  rcases hu : unpackAux w [] with _ | ⟨u, rest⟩
  · simp
  · obtain ⟨v, s', hv, hs, _⟩ := unpackAux_cons_spec w [] u rest hu
    simp at hv; subst hv
    simp [hs, packOne_length]; omega

theorem packOne_len (x : Bits) : (packOne x).length = 2 * x.length + 1 := by
  rw [packOne_length]

theorem hdisjD (hnd : outW.Nodup) (hL : outW.length = L) :
    ∀ j ∈ jobsD L h outW, ∀ j' ∈ jobsD L h outW, ∀ c ∈ j.1, c.1 ≠ j'.2 := by
  intro j hj j' hj' c hc
  obtain ⟨_, h2, _, _⟩ := jobsD_ctrl L h outW hnd hL j hj
  obtain ⟨_, _, _, i, _, hi⟩ := jobsD_ctrl L h outW hnd hL j' hj'
  obtain ⟨k, hk⟩ := h2 c hc
  rw [hk, hi]; exact (fw_ne_eL L h i k).symm

theorem hdisjE (hnd : outW.Nodup) (hL : outW.length = L) :
    ∀ j ∈ jobsE L h outW, ∀ j' ∈ jobsE L h outW, ∀ c ∈ j.1, c.1 ≠ j'.2 := by
  intro j hj j' hj' c hc
  obtain ⟨_, h2, _, _⟩ := jobsE_ctrl L h outW hnd hL j hj
  obtain ⟨_, _, _, i, hi, hi'⟩ := jobsE_ctrl L h outW hnd hL j' hj'
  rw [hi']
  rcases h2 c hc with ⟨k, hk⟩ | ⟨k, hk, hk'⟩
  · rw [hk]; exact (fw_ne_eL L h _ k).symm
  · rw [hk']; intro hh; have := fw_inj L h _ _ (by omega) (by omega) hh; omega

theorem effD_tgt (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') (k : Fin N')
    (hk : ∀ i < L, k ≠ fw L h i) : eff (jobsD L h outW) y k = false :=
  eff_notarget _ _ _ fun j hj => by
    obtain ⟨_, _, _, i, hi, hi'⟩ := jobsD_ctrl L h outW hnd hL j hj
    rw [hi']; exact (hk i hi).symm

theorem effE_tgt (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') (k : Fin N')
    (hk : ∀ i < 2 * L + 2, k ≠ fw L h (L + 1 + i)) : eff (jobsE L h outW) y k = false :=
  eff_notarget _ _ _ fun j hj => by
    obtain ⟨_, _, _, i, hi, hi'⟩ := jobsE_ctrl L h outW hnd hL j hj
    rw [hi']; exact (hk i hi).symm

theorem effD_R (hL : outW.length = L) (y : Qubits N') (i : ℕ) (hi : i < L + 1) :
    eff (jobsD L h outW) y (fw L h i) =
      (packOne (decodeOne (readWires outW (y ∘ eL h)))).getD i false := by
  have hinj : InjBelow (Rw L h) (L + 1) := by
    intro a b ha hb hab; exact fw_inj L h _ _ (by omega) (by omega) hab
  have := eff_dJobs_top (Rw L h) (L + 1) hinj y (wsL L h outW) (by simp [wsL, hL]) i hi
  rw [show fw L h i = Rw L h i from rfl, jobsD, this]
  simp [wsL, readWires, List.map_map]

theorem jD_apply (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') (k : Fin N') :
    jobsFun (jobsD L h outW) y k = xor (y k) (eff (jobsD L h outW) y k) :=
  jobsFun_eq _ (hdisjD L h outW hnd hL) y k

theorem jE_apply (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') (k : Fin N') :
    jobsFun (jobsE L h outW) y k = xor (y k) (eff (jobsE L h outW) y k) :=
  jobsFun_eq _ (hdisjE L h outW hnd hL) y k

theorem jD_invol (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') :
    jobsFun (jobsD L h outW) (jobsFun (jobsD L h outW) y) = y := by
  funext k
  rw [jD_apply L h outW hnd hL, jD_apply L h outW hnd hL,
    eff_congr _ (jobsFun (jobsD L h outW) y) y (fun j hj c hc => by
      rw [jD_apply L h outW hnd hL]
      obtain ⟨_, h2, _, _⟩ := jobsD_ctrl L h outW hnd hL j hj
      obtain ⟨i, hi⟩ := h2 c hc
      rw [hi, effD_tgt L h outW hnd hL y _ (fun i' _ => (fw_ne_eL L h i' i).symm)]; simp)]
  simp

theorem jE_invol (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') :
    jobsFun (jobsE L h outW) (jobsFun (jobsE L h outW) y) = y := by
  funext k
  rw [jE_apply L h outW hnd hL, jE_apply L h outW hnd hL,
    eff_congr _ (jobsFun (jobsE L h outW) y) y (fun j hj c hc => by
      rw [jE_apply L h outW hnd hL]
      obtain ⟨_, h2, _, _⟩ := jobsE_ctrl L h outW hnd hL j hj
      rw [effE_tgt L h outW hnd hL y]; · simp
      intro i' hi'
      rcases h2 c hc with ⟨k, hk⟩ | ⟨k, hk, hk'⟩
      · rw [hk]; exact (fw_ne_eL L h _ k).symm
      · rw [hk']; intro hh; have := fw_inj L h _ _ (by omega) (by omega) hh; omega)]
  simp


theorem clf_iff (z : Qubits N') : clf L (z ∘ fL h) ↔ ∀ a ∈ ancL L h, z a = false := by
  constructor
  · intro H a ha
    rw [mem_ancL] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    have := H i hi
    rw [Function.comp_apply, ← fw_eq_fL] at this
    exact this
  · intro H i hi
    rw [Function.comp_apply, ← fw_eq_fL]
    exact H _ ((mem_ancL L h _).2 ⟨i, hi, rfl⟩)

theorem jD_eL (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') :
    jobsFun (jobsD L h outW) y ∘ eL h = y ∘ eL h := by
  funext i
  simp only [Function.comp_apply]
  rw [jD_apply L h outW hnd hL, effD_tgt L h outW hnd hL y _ (fun i' _ => (fw_ne_eL L h i' i).symm)]
  simp

theorem jE_eL (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') :
    jobsFun (jobsE L h outW) y ∘ eL h = y ∘ eL h := by
  funext i
  simp only [Function.comp_apply]
  rw [jE_apply L h outW hnd hL, effE_tgt L h outW hnd hL y _ (fun i' _ => (fw_ne_eL L h _ i).symm)]
  simp

theorem jD_cl (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') :
    clf L (jobsFun (jobsD L h outW) y ∘ fL h) ↔ clf L (y ∘ fL h) := by
  rw [clf_iff, clf_iff]
  have : ∀ a ∈ ancL L h, jobsFun (jobsD L h outW) y a = y a := by
    intro a ha
    rw [mem_ancL] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    rw [jD_apply L h outW hnd hL, effD_tgt L h outW hnd hL]; · simp
    intro i' hi' hh; have := fw_inj L h _ _ (by omega) (by omega) hh; omega
  exact ⟨fun H a ha => by rw [← this a ha]; exact H a ha, fun H a ha => by rw [this a ha]; exact H a ha⟩

theorem jE_cl (hnd : outW.Nodup) (hL : outW.length = L) (y : Qubits N') :
    clf L (jobsFun (jobsE L h outW) y ∘ fL h) ↔ clf L (y ∘ fL h) := by
  rw [clf_iff, clf_iff]
  have : ∀ a ∈ ancL L h, jobsFun (jobsE L h outW) y a = y a := by
    intro a ha
    rw [mem_ancL] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    rw [jE_apply L h outW hnd hL, effE_tgt L h outW hnd hL]; · simp
    intro i' hi' hh; have := fw_inj L h _ _ (by omega) (by omega) hh; omega
  exact ⟨fun H a ha => by rw [← this a ha]; exact H a ha, fun H a ha => by rw [this a ha]; exact H a ha⟩

theorem jobsD_pre (hnd : outW.Nodup) (hL : outW.length = L) :
    ∀ j ∈ jobsD L h outW, (j.2 :: (j.1.map Prod.fst ++ ancL L h)).Nodup ∧
      j.1.length ≤ (ancL L h).length + 1 := by
  intro j hj
  obtain ⟨h1, h2, h3, i, hi, hi'⟩ := jobsD_ctrl L h outW hnd hL j hj
  refine ⟨?_, by simp [ancL]; omega⟩
  rw [List.nodup_cons, List.nodup_append]
  refine ⟨?_, h1, ancL_nodup L h, ?_⟩
  · rw [List.mem_append, hi']
    rintro (hm | hm)
    · obtain ⟨c, hc, hc'⟩ := List.mem_map.1 hm
      obtain ⟨k, hk⟩ := h2 c hc
      rw [hc'] at hk; exact fw_ne_eL L h i k hk
    · rw [mem_ancL] at hm; obtain ⟨i', _, hh⟩ := hm
      have := fw_inj L h _ _ (by omega) (by omega) hh; omega
  · intro a ha b hb hab
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨k, hk⟩ := h2 c hc
    rw [mem_ancL] at hb; obtain ⟨i', _, rfl⟩ := hb
    rw [hk] at hab; exact fw_ne_eL L h _ k hab.symm

theorem jobsE_pre (hnd : outW.Nodup) (hL : outW.length = L) :
    ∀ j ∈ jobsE L h outW, (j.2 :: (j.1.map Prod.fst ++ ancL L h)).Nodup ∧
      j.1.length ≤ (ancL L h).length + 1 := by
  intro j hj
  obtain ⟨h1, h2, h3, i, hi, hi'⟩ := jobsE_ctrl L h outW hnd hL j hj
  refine ⟨?_, by simp [ancL]; omega⟩
  rw [List.nodup_cons, List.nodup_append]
  refine ⟨?_, h1, ancL_nodup L h, ?_⟩
  · rw [List.mem_append, hi']
    rintro (hm | hm)
    · obtain ⟨c, hc, hc'⟩ := List.mem_map.1 hm
      rcases h2 c hc with ⟨k, hk⟩ | ⟨k, hk, hk'⟩
      · rw [hc'] at hk; exact fw_ne_eL L h _ k hk
      · rw [hc'] at hk'; have := fw_inj L h _ _ (by omega) (by omega) hk'; omega
    · rw [mem_ancL] at hm; obtain ⟨i', _, hh⟩ := hm
      have := fw_inj L h _ _ (by omega) (by omega) hh; omega
  · intro a ha b hb hab
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    rw [mem_ancL] at hb; obtain ⟨i', _, rfl⟩ := hb
    rcases h2 c hc with ⟨k, hk⟩ | ⟨k, hk, hk'⟩
    · rw [hk] at hab; exact fw_ne_eL L h _ k hab.symm
    · rw [hk'] at hab; have := fw_inj L h _ _ (by omega) (by omega) hab; omega

end Layout2

theorem getD_pad (l : Bits) (M i : ℕ) :
    (l ++ List.replicate M false).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with hi
  · rfl
  · rw [List.getElem?_eq_none (by omega : l.length ≤ i), List.getElem?_replicate]
    split_ifs <;> simp

theorem packOne_getD_inj (x x' : Bits) (M : ℕ) (hx : 2 * x.length + 1 ≤ M)
    (hx' : 2 * x'.length + 1 ≤ M)
    (hh : ∀ j < M, (packOne x).getD j false = (packOne x').getD j false) : x = x' := by
  have e1 := range_getD (packOne x) M (by rw [packOne_len]; exact hx)
  have e2 := range_getD (packOne x') M (by rw [packOne_len]; exact hx')
  have e : (List.range M).map (fun i => (packOne x).getD i false) =
      (List.range M).map (fun i => (packOne x').getD i false) := by
    apply List.map_congr_left; intro j hj; exact hh j (List.mem_range.1 hj)
  rw [e1, e2] at e
  have := congrArg (fun s => unpackAux s []) e
  simp only [unpackAux_packOne] at this
  simp at this
  exact this.1

/-- The fresh configuration recording `u` in `R`. -/
def fstar (L : ℕ) (u : Bits) : Qubits (5 * L + 7) :=
  fun j => if j.val < L + 1 then (packOne u).getD j.val false else false

theorem clf_fstar (L : ℕ) (u : Bits) : clf L (fstar L u) := by
  intro i hi; simp [fstar]; omega

section Layout3
variable {N N' : ℕ} (L : ℕ) (h : N + (5 * L + 7) = N') (outW : List (Fin N))

theorem jn_fw (p : Qubits N) (q : Qubits (5 * L + 7)) (k : ℕ) (hk : k < 5 * L + 7) :
    jn h p q (fw L h k) = q ⟨k, hk⟩ := by
  rw [fw_eq_fL L h ⟨k, hk⟩]
  exact congrFun (jn_f h p q) ⟨k, hk⟩

theorem hstar_layout (hnd : outW.Nodup) (hL : outW.length = L) (u : Bits) (hu : 2 * u.length + 1 ≤ L + 1)
    (p : Qubits N) :
    (jobsFun (jobsD L h outW) (jn h p (fstar L u)) ∘ fL h = fun _ => false) ↔
      decodeOne (readWires outW p) = u := by
  have hdl : 2 * (decodeOne (readWires outW p)).length + 1 ≤ L + 1 := by
    have := decodeOne_len (readWires outW p)
    have hlen : (readWires outW p).length = L := by simp [readWires, hL]
    omega
  have key : ∀ j : Fin (5 * L + 7), (jobsFun (jobsD L h outW) (jn h p (fstar L u)) ∘ fL h) j =
      xor (fstar L u j) (if j.val < L + 1 then
        (packOne (decodeOne (readWires outW p))).getD j.val false else false) := by
    intro j
    rw [Function.comp_apply, ← fw_eq_fL, jD_apply L h outW hnd hL, jn_fw L h p _ j.val j.isLt]
    congr 1
    split_ifs with hj
    · rw [effD_R L h outW hL _ _ hj, jn_e]
    · apply effD_tgt L h outW hnd hL
      intro i hi hh; have := fw_inj L h _ _ j.isLt (by omega) hh; omega
  constructor
  · intro H
    apply (packOne_getD_inj _ _ (L + 1) hdl hu _)
    intro j hj
    have := key ⟨j, by omega⟩
    rw [H] at this
    simp only [fstar, hj, if_true] at this
    revert this; cases (packOne u).getD j false <;> cases (packOne (decodeOne (readWires outW p))).getD j false <;> simp
  · intro H
    funext j
    rw [key, H]
    simp only [fstar]
    split_ifs <;> simp

theorem effE_O (hnd : outW.Nodup) (hL : outW.length = L) (u : Bits) (hu : 2 * u.length + 1 ≤ L + 1)
    (p : Qubits N) (i : ℕ) (hi : i < 2 * L + 2) :
    eff (jobsE L h outW) (jn h p (fstar L u)) (Ow L h i) =
      (packOne u ++ packOne (decodeOne (readWires outW p))).getD i false := by
  set y := jn h p (fstar L u)
  have hinj : InjBelow (Ow L h) (2 * L + 2) := by
    intro a b ha hb hab; have := fw_inj L h _ _ (by omega) (by omega) hab; omega
  have hr : (rws L h).map y = packOne u ++ List.replicate (L + 1 - (packOne u).length) false := by
    rw [← range_getD _ _ (by rw [packOne_len]; exact hu), rws, List.map_map]
    apply List.map_congr_left; intro j hj
    have hj' := List.mem_range.1 hj
    simp only [Function.comp_apply, Rw, y]
    rw [jn_fw L h p _ j (by omega)]
    simp [fstar, hj']
  rw [jobsE, eff_append, eff_copyJobs (Ow L h) (2 * L + 2) hinj y (rws L h) i (by simp [rws]; omega) hi,
    eff_eJobs (Ow L h) (2 * L + 2) hinj y (wsL L h outW) u [] (rws L h) _ i hi
      (by simp [rws, wsL, hL]; omega) rfl hr, hr, getD_pad]
  have hw : (wsL L h outW).map y = readWires outW p := by
    simp only [wsL, List.map_map, readWires]
    congr 1; funext a; simp only [Function.comp_apply, y]; exact congrFun (jn_e h p _) a
  rw [hw, dOut_eq]
  by_cases hi2 : i < 2 * u.length + 1
  · rw [List.getD_append _ _ _ _ (by rw [packOne_len]; exact hi2)]
    simp [show ¬ (2 * u.length + 1 ≤ i) by omega]
  · rw [List.getD_append_right _ _ _ _ (by rw [packOne_len]; omega),
      List.getD_eq_default _ _ (by rw [packOne_len]; omega), packOne_len]
    simp [show (2 * u.length + 1 ≤ i) by omega]

theorem readO (hnd : outW.Nodup) (hL : outW.length = L) (u : Bits) (hu : 2 * u.length + 1 ≤ L + 1)
    (p : Qubits N) :
    readWires (ows L h) (jobsFun (jobsE L h outW) (jn h p (fstar L u))) =
      packOne u ++ packOne (decodeOne (readWires outW p)) ++
        List.replicate (2 * L + 2 - (packOne u ++ packOne (decodeOne (readWires outW p))).length) false := by
  have hdl : 2 * (decodeOne (readWires outW p)).length + 1 ≤ L + 1 := by
    have := decodeOne_len (readWires outW p)
    have hlen : (readWires outW p).length = L := by simp [readWires, hL]
    omega
  rw [← range_getD _ _ (by simp [packOne_len]; omega), readWires, ows, List.map_map]
  apply List.map_congr_left; intro i hi
  have hi' := List.mem_range.1 hi
  simp only [Function.comp_apply]
  rw [jE_apply L h outW hnd hL, effE_O L h outW hnd hL u hu p i hi', Ow,
    jn_fw L h p _ _ (by omega)]
  have : ¬ (L + 1 + i < L + 1) := by omega
  simp [fstar, this]

theorem unpack_two (a b : Bits) (k : ℕ) :
    (unpack (packOne a ++ packOne b ++ List.replicate k false)).getD 0 [] = a ∧
    (unpack (packOne a ++ packOne b ++ List.replicate k false)).getD 1 [] = b := by
  unfold unpack
  rw [List.append_assoc, unpackAux_packOne, unpackAux_packOne]
  simp

end Layout3

section Sprime
variable (S : QStrategy) (r : ℕ)

abbrev Lof : ℕ := (S.stepAt r).outW.length

abbrev mOf : ℕ := 5 * Lof S r + 7

theorem hN : S.N + mOf S r = S.inQ + (S.wkQ + mOf S r) := by
  simp only [QStrategy.N]; omega

noncomputable def finalCirc : QCircuit (S.inQ + (S.wkQ + mOf S r)) :=
  liftCirc (hN S r) (S.stepAt r).circ ++
    jobsCirc (jobsD (Lof S r) (hN S r) (S.stepAt r).outW) (ancL (Lof S r) (hN S r)) ++
    liftCirc (hN S r) (QCircuit.adj (S.stepAt r).circ) ++
    liftCirc (hN S r) (flipCirc (S.stepAt r).inW) ++
    liftCirc (hN S r) (S.stepAt r).circ ++
    jobsCirc (jobsE (Lof S r) (hN S r) (S.stepAt r).outW) (ancL (Lof S r) (hN S r))

noncomputable def finalStep : RoundStep (S.inQ + (S.wkQ + mOf S r)) :=
  ⟨[], finalCirc S r, ows (Lof S r) (hN S r)⟩

noncomputable def Sprime : QStrategy where
  inQ := S.inQ
  wkQ := S.wkQ + mOf S r
  advice := fun z => S.advice (fun i => z (Fin.castAdd _ i)) *
    (if ∀ j : Fin (mOf S r), z (Fin.natAdd S.wkQ j) = false then 1 else 0)
  steps := (S.steps.take r).map (liftStep (hN S r)) ++ [finalStep S r]

theorem hN' : S.N + mOf S r = (Sprime S r).N := hN S r

theorem Sprime_stepAt_lt (hr : r < S.steps.length) (j : ℕ) (hj : j < r) :
    (Sprime S r).stepAt j = liftStep (hN' S r) (S.stepAt j) := by
  have hj' : j < S.steps.length := by omega
  simp only [QStrategy.stepAt, Sprime, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_take_of_lt hj,
    List.getElem?_eq_getElem hj']
  rfl

theorem Sprime_stepAt_r (hr : r < S.steps.length) : (Sprime S r).stepAt r = finalStep S r := by
  simp only [QStrategy.stepAt, Sprime]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [Nat.min_eq_left hr.le]

theorem Sprime_initDM (ρ : Matrix (Qubits S.inQ) (Qubits S.inQ) ℂ) :
    (Sprime S r).initDM ρ = tens (hN' S r) (S.initDM ρ) (zeroDM (mOf S r)) := by
  ext y z
  dsimp only [QStrategy.initDM, tens, zeroDM, Sprime]
  erw [Matrix.of_apply, Matrix.of_apply]
  have hf : ∀ x : Qubits (S.inQ + (S.wkQ + mOf S r)), fstPart (a := S.inQ) x = fstPart (x ∘ eL (hN' S r)) := by
    intro x; funext i; simp only [fstPart, Function.comp_apply]; congr 1
  have hs : ∀ x : Qubits (S.inQ + (S.wkQ + mOf S r)),
      (fun i => sndPart (a := S.inQ) x (Fin.castAdd (mOf S r) i)) = sndPart (x ∘ eL (hN' S r)) := by
    intro x; funext i; simp only [sndPart, Function.comp_apply]; congr 1
  have hz : ∀ x : Qubits (S.inQ + (S.wkQ + mOf S r)),
      (∀ j : Fin (mOf S r), sndPart (a := S.inQ) x (Fin.natAdd S.wkQ j) = false) ↔
        x ∘ fL (hN' S r) = fun _ => false := by
    intro x
    constructor
    · intro H; funext j; have := H j; simp only [sndPart] at this
      simp only [Function.comp_apply]; convert this using 2; apply Fin.ext
      simp only [Fin.val_natAdd, fL, QStrategy.N]; omega
    · intro H j; have := congrFun H j; simp only [Function.comp_apply] at this
      simp only [sndPart]; convert this using 2; apply Fin.ext
      simp only [Fin.val_natAdd, fL, QStrategy.N]; omega
  erw [Matrix.of_apply, Matrix.of_apply]
  rw [hf y, hf z, hs y, hs z]
  simp only [hz y, hz z]
  split_ifs <;> simp_all <;> rfl

theorem Sprime_run (hr : r < S.steps.length) (msg : List Bits → Bits) (os : List Bits)
    (hos : os.length = r) (ρ : Matrix (Qubits S.inQ) (Qubits S.inQ) ℂ) :
    (Sprime S r).run msg ρ os = tens (hN' S r) (S.run msg ρ os) (zeroDM (mOf S r)) := by
  simp only [QStrategy.run]
  erw [Sprime_initDM S r ρ]
  exact runFrom_lift S (Sprime S r) (hN' S r) r (fun j hj => Sprime_stepAt_lt S r hr j hj) msg msg
    (fun _ _ => rfl) _ os [] _ (by simp [hos])

end Sprime

section Branch
variable (Cm : CommitmentScheme) (S : QStrategy) (n : ℕ)

/-- The open-both acceptance predicate on the output string. -/
def okf (c : CoinSpace (Cm.receiver.coins (Cm.setup n))) (os : List Bits) (s : Bits) : Bool :=
  let u0 := (unpack s).getD 0 []
  let u1 := (unpack s).getD 1 []
  let ok : Bool → Bool := fun b =>
    Cm.ropen [b] u0 (commTranscript Cm n c os) (encCoins c) (Cm.setup n) ||
      Cm.ropen [b] u1 (commTranscript Cm n c os) (encCoins c) (Cm.setup n)
  ok false && ok true

theorem nv_zero_dg {ι : Type*} [Fintype ι] [DecidableEq ι] (q1 q0 : ι → Bool) (W : Matrix ι ι ℂ)
    (B : Matrix ι Unit ℂ) (h0 : ∀ z, q0 z = false) : nv (dg q1 * (W * (dg q0 * B))) = 0 := by
  have : dg q0 * B = 0 := by
    ext i u; rw [dg_apply_vec, h0]; simp
  rw [this, Matrix.mul_zero, Matrix.mul_zero, nv_eq]; simp

theorem stepAt_mem (hr : Cm.rounds n < S.steps.length) : S.stepAt (Cm.rounds n) ∈ S.steps := by
  simp only [QStrategy.stepAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact List.getElem_mem hr

theorem branch_S' (hV : S.Valid) (huo : Cm.HasUniqueOpenings) (hr : Cm.rounds n < S.steps.length)
    (c : CoinSpace (Cm.receiver.coins (Cm.setup n))) (os : List Bits) :
    qval Cm S n c os ≤
      nv (dg (fun z => okf Cm n c os (readWires (ows (Lof S (Cm.rounds n)) (hN S (Cm.rounds n))) z)) *
        ((finalStep S (Cm.rounds n)).op [] *
          tv (hN S (Cm.rounds n)) (pureOf S (expMsg Cm n c fun _ => []) os) e0)) ^ 2 := by
  set r := Cm.rounds n
  set L := Lof S r
  set h := hN S r
  set st := S.stepAt r
  set B := pureOf S (expMsg Cm n c fun _ => []) os
  have hnd : st.outW.Nodup := (hV.2 st (stepAt_mem Cm S n hr)).2
  have hL : st.outW.length = L := rfl
  by_cases hex : ∃ p0, qb Cm S n false c os p0 = true
  swap
  · push_neg at hex
    rw [qval, nv_zero_dg _ _ _ _ (fun z => by simpa using hex z)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  obtain ⟨p0, hp0⟩ := hex
  have hu : 2 * (decodeOne (readWires st.outW p0)).length + 1 ≤ L + 1 := by
    have := decodeOne_len (readWires st.outW p0)
    have hlen : (readWires st.outW p0).length = L := by simp [readWires, hL]
    omega
  set u := decodeOne (readWires st.outW p0)
  have hq0 : ∀ p, qb Cm S n false c os p = true ↔ decodeOne (readWires st.outW p) = u := by
    intro p
    constructor
    · intro hp; exact huo _ _ _ false _ _ hp hp0
    · intro hp; simp only [qb] at hp0 ⊢; rw [hp]; exact hp0
  obtain ⟨FD, hFD, hFDz⟩ := jobs_spec (jobsD L h st.outW) (ancL L h) (jobsD_pre L h st.outW hnd hL)
  obtain ⟨FE, hFE, hFEz⟩ := jobs_spec (jobsE L h st.outW) (ancL L h) (jobsE_pre L h st.outW hnd hL)
  have hop : (finalStep S r).op [] = permOf FE * (embedOp (Wop Cm S n) (eL h) *
      (permOf FD * embedOp (st.op [false]) (eL h))) := by
    rw [op_nil]
    simp only [finalStep, finalCirc, circuit_unitary_append, liftCirc_unitary, QCircuit.adj_unitary,
      flipCirc_unitary]
    rw [show (jobsCirc (jobsD L h st.outW) (ancL L h)).unitary = permOf FD from hFD,
      show (jobsCirc (jobsE L h st.outW) (ancL L h)).unitary = permOf FE from hFE]
    simp only [Wop, RoundStep.op, loadX_false, Matrix.mul_one, embedOp_mul, Matrix.mul_assoc]
    rfl
  rw [hop, qval]
  simp only [Matrix.mul_assoc]
  refine main_bound h (st.op [false]) (Wop Cm S n) B FD FE (jobsFun (jobsD L h st.outW))
    (jobsFun (jobsE L h st.outW)) (clf L) (qb Cm S n false c os) (qb Cm S n true c os) _ (fstar L u)
    (fun y hy => hFDz y ((clf_iff L h y).1 hy)) (jD_invol L h st.outW hnd hL) (jD_cl L h st.outW hnd hL)
    (jD_eL L h st.outW hnd hL) (fun y hy => hFEz y ((clf_iff L h y).1 hy)) (jE_invol L h st.outW hnd hL)
    (jE_cl L h st.outW hnd hL) (fun i hi => rfl)
    (fun p => (hstar_layout L h st.outW hnd hL u hu p).trans (hq0 p).symm) ?_
  intro p hp
  rw [readO L h st.outW hnd hL u hu p]
  obtain ⟨h0, h1⟩ := unpack_two u (decodeOne (readWires st.outW p))
    (2 * L + 2 - (packOne u ++ packOne (decodeOne (readWires st.outW p))).length)
  simp only [okf, h0, h1]
  have e0 : Cm.ropen [false] u (commTranscript Cm n c os) (encCoins c) (Cm.setup n) = true := hp0
  have e1 : Cm.ropen [true] (decodeOne (readWires st.outW p)) (commTranscript Cm n c os) (encCoins c)
      (Cm.setup n) = true := hp
  simp [e0, e1]

end Branch

section OpenBoth
variable (Cm : CommitmentScheme) (n : ℕ)

noncomputable def obT (T : QStrategy) (c : CoinSpace (Cm.receiver.coins (Cm.setup n))) (os : List Bits) : ℝ :=
  if okf Cm n c (os.take (Cm.rounds n)) (os.getD (Cm.rounds n) []) = true then
    (T.run (expMsg Cm n c (fun _ => [])) (zeroDM T.inQ) os).trace.re
  else 0

theorem openBoth_eq (T : QStrategy) : openBothProb Cm T n =
    avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
      ∑ o : T.Outs (Cm.rounds n), ∑ x : Qubits (T.stepAt (Cm.rounds n)).outW.length,
        obT Cm n T c (QStrategy.outList o ++ [List.ofFn x]) := by
  have : openBothProb Cm T n = avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
      ∑ o : T.Outs (Cm.rounds n + 1), obT Cm n T c (QStrategy.outList o) := rfl
  rw [this]
  congr 1; funext c
  exact sum_outs_succ T (Cm.rounds n) (obT Cm n T c)

theorem ob_branch (T : QStrategy) (c : CoinSpace (Cm.receiver.coins (Cm.setup n)))
    (o : T.Outs (Cm.rounds n)) (Bv : Matrix (Qubits T.N) Unit ℂ)
    (hB : T.run (expMsg Cm n c fun _ => []) (zeroDM T.inQ) (QStrategy.outList o) = Bv * Bvᴴ) :
    (∑ x : Qubits (T.stepAt (Cm.rounds n)).outW.length,
        obT Cm n T c (QStrategy.outList o ++ [List.ofFn x])) =
      nv (dg (fun z => okf Cm n c (QStrategy.outList o)
        (readWires (T.stepAt (Cm.rounds n)).outW z)) * ((T.stepAt (Cm.rounds n)).op [] * Bv)) ^ 2 := by
  set os := QStrategy.outList o
  have hlen : os.length = Cm.rounds n := outList_length T o
  have hrun : ∀ y : Bits, T.run (expMsg Cm n c (fun _ => [])) (zeroDM T.inQ) (os ++ [y]) =
      stepDM (T.stepAt (Cm.rounds n)) [] y (Bv * Bvᴴ) := by
    intro y
    rw [← hB, QStrategy.run, QStrategy.run, runFrom_snoc]
    simp only [List.nil_append, hlen]
    have hm : expMsg Cm n c (fun _ => []) os = [] := by simp [expMsg, hlen]
    rw [hm]
  refine Eq.trans ?_ (meas_pred (T.stepAt (Cm.rounds n)) [] Bv (okf Cm n c os))
  apply Finset.sum_congr rfl
  intro x _
  have ht : ∀ y : Bits, (os ++ [y]).take (Cm.rounds n) = os := by
    intro y; rw [← hlen]; simp
  have hg : ∀ y : Bits, (os ++ [y]).getD (Cm.rounds n) [] = y := by
    intro y; rw [← hlen]; simp
  rw [obT, ht, hg, hrun]

theorem avgOver_mono {α : Type*} [Fintype α] (f g : α → ℝ) (h : ∀ a, f a ≤ g a) :
    avgOver α f ≤ avgOver α g := by
  simp only [avgOver, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => h a) (by positivity)

theorem lens_eq_Sprime (S : QStrategy) (r : ℕ) (hr : r < S.steps.length) :
    (List.range r).map (fun j => ((Sprime S r).stepAt j).outW.length) =
      (List.range r).map (fun j => (S.stepAt j).outW.length) := by
  apply List.map_congr_left
  intro j hj
  rw [Sprime_stepAt_lt S r hr j (List.mem_range.1 hj)]
  simp [liftStep]

theorem openBoth_Sprime_ge (S : QStrategy) (hV : S.Valid) (huo : Cm.HasUniqueOpenings)
    (hr : Cm.rounds n < S.steps.length) :
    (avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
      ∑ o : S.Outs (Cm.rounds n), qval Cm S n c (QStrategy.outList o)) ≤
      openBothProb Cm (Sprime S (Cm.rounds n)) n := by
  rw [openBoth_eq]
  apply avgOver_mono
  intro c
  set r := Cm.rounds n
  have hconv : ∀ F : List Bits → ℝ, (∑ o : (Sprime S r).Outs r, F (QStrategy.outList o)) =
      ∑ o : S.Outs r, F (QStrategy.outList o) := by
    intro F
    rw [sum_outs_eq', sum_outs_eq', lens_eq_Sprime S r hr]
  rw [← hconv]
  apply Finset.sum_le_sum
  intro o _
  have hlen : (QStrategy.outList o).length = r := outList_length _ o
  have hB : (Sprime S r).run (expMsg Cm n c fun _ => []) (zeroDM (Sprime S r).inQ)
      (QStrategy.outList o) =
      tv (hN' S r) (pureOf S (expMsg Cm n c fun _ => []) (QStrategy.outList o)) e0 *
        (tv (hN' S r) (pureOf S (expMsg Cm n c fun _ => []) (QStrategy.outList o)) e0)ᴴ := by
    refine (Sprime_run S r hr _ _ hlen (zeroDM S.inQ)).trans ?_
    rw [pureOf_spec, tens_pure]
  rw [ob_branch Cm n (Sprime S r) c o _ hB, Sprime_stepAt_r S r hr]
  exact branch_S' Cm S n hV huo hr c (QStrategy.outList o)

end OpenBoth

section Short
variable (Cm : CommitmentScheme) (n : ℕ)

theorem loadX_nilW {N : ℕ} (x : Bits) : loadX ([] : List (Fin N)) x = 1 := by
  ext y z
  simp [loadX, flipMask, Matrix.one_apply]

theorem openBoth_short_ge (S : QStrategy) (hr : S.steps.length ≤ Cm.rounds n) :
    (avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
      ∑ o : S.Outs (Cm.rounds n), qval Cm S n c (QStrategy.outList o)) ≤
      openBothProb Cm S n := by
  rw [openBoth_eq]
  apply avgOver_mono
  intro c
  apply Finset.sum_le_sum
  intro o _
  rw [ob_branch Cm n S c o _ (pureOf_spec _ _ _)]
  set B := pureOf S (expMsg Cm n c fun _ => []) (QStrategy.outList o)
  have hst : S.stepAt (Cm.rounds n) = default := by
    simp only [QStrategy.stepAt]; exact List.getD_eq_default _ _ hr
  have hop : ∀ x, (S.stepAt (Cm.rounds n)).op x = 1 := by
    intro x; rw [hst]; simp [RoundStep.op, default, Circuit.unitary, loadX_nilW]
  have hW : Wop Cm S n = 1 := by rw [Wop, hop, hop]; simp
  rw [qval, hW, hop, hop]; simp only [Matrix.one_mul]
  apply le_of_eq
  rw [nv_dg_sq, nv_dg_sq]
  apply Finset.sum_congr rfl; intro z _
  rw [dg_apply_vec]
  have hrw : ∀ z : Qubits S.N, readWires (S.stepAt (Cm.rounds n)).outW z = [] := by
    intro z; rw [hst]; rfl
  simp only [qb, okf, hrw, decodeOne, unpack, unpackAux, List.headD_nil, List.getD_nil]
  split_ifs <;> simp_all <;> rfl

end Short

section Size

theorem xIf_len {n : ℕ} (a : Fin n) (α : Bool) : (xIf a α).length ≤ 1 := by
  cases α <;> simp [xIf]

theorem cnotP_len {n : ℕ} (a : Fin n) (α : Bool) (t : Fin n) : (cnotP a α t).length ≤ 3 := by
  unfold cnotP; split_ifs
  · simp only [List.length_append, List.length_singleton]
    have := xIf_len a α; omega
  · simp

theorem toffP_len {n : ℕ} (a : Fin n) (α : Bool) (b : Fin n) (β : Bool) (t : Fin n) :
    (toffP a α b β t).length ≤ 9 := by
  unfold toffP; split_ifs
  · simp only [List.length_append, toffCirc, List.length_cons, List.length_nil]
    have := xIf_len a α; have := xIf_len b β; omega
  · simp

theorem mcx_len {n : ℕ} : ∀ (cs : List (Fin n × Bool)) (t : Fin n) (anc : List (Fin n)),
    (mcx cs t anc).length ≤ 20 * (cs.length + 1)
  | [], t, anc => by simp [mcx]
  | [(c, α)], t, anc => by
      simp only [mcx]; have := cnotP_len c α t; simp; omega
  | (c₁, α₁) :: (c₂, α₂) :: rest, t, anc => by
      match anc with
      | [] => simp [mcx]
      | a :: anc' =>
        simp only [mcx, List.length_append]
        have h1 := toffP_len c₁ α₁ c₂ α₂ a
        have h2 := mcx_len ((a, true) :: rest) t anc'
        simp only [List.length_cons] at h2 ⊢
        omega

theorem jobsCirc_len {n : ℕ} (jobs : List (Job n)) (anc : List (Fin n)) (B : ℕ)
    (hB : ∀ j ∈ jobs, j.1.length ≤ B) : (jobsCirc jobs anc).length ≤ jobs.length * (20 * (B + 1)) := by
  induction jobs with
  | nil => simp [jobsCirc]
  | cons j l ih =>
    have h1 := mcx_len j.1 j.2 anc
    have h2 := ih (fun j' hj' => hB j' (List.mem_cons_of_mem _ hj'))
    have h3 := hB j List.mem_cons_self
    simp only [jobsCirc, List.flatMap_cons, List.length_append] at h2 ⊢
    simp only [List.length_cons]
    have : 20 * (j.1.length + 1) ≤ 20 * (B + 1) := by omega
    nlinarith

theorem termJobs_len {n : ℕ} (tgt : ℕ → Fin n) (P : List (Fin n × Bool)) (ds : List (Fin n)) :
    (termJobs tgt P ds).length = 2 * ds.length := by
  induction ds generalizing tgt with
  | nil => simp [termJobs]
  | cons d ds ih => simp [termJobs, ih]; ring

theorem dJobs_len {n : ℕ} (tgt : ℕ → Fin n) : ∀ (pre : List (Fin n × Bool)) (ds ws : List (Fin n)),
    (dJobs tgt pre ds ws).length ≤ ws.length * (2 * (ds.length + ws.length))
  | pre, ds, f :: d :: rest => by
      rw [dJobs, List.length_append, termJobs_len]
      have := dJobs_len tgt (pre ++ [(f, true)]) (ds ++ [d]) rest
      simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
      nlinarith
  | pre, ds, [f] => by rw [dJobs, termJobs_len]; simp
  | pre, ds, [] => by simp [dJobs]

theorem eJobs_len {n : ℕ} (tgt : ℕ → Fin n) : ∀ (pre : List (Fin n × Bool)) (rws ws : List (Fin n)),
    (eJobs tgt pre rws ws).length ≤ rws.length * (2 * ws.length * ws.length)
  | pre, rf :: rd :: rrest, ws => by
      rw [eJobs, List.length_append]
      have h1 := dJobs_len (fun i => tgt (i + 1)) (pre ++ [(rf, false)]) [] ws
      have h2 := eJobs_len (fun i => tgt (i + 2)) (pre ++ [(rf, true)]) rrest ws
      simp only [List.length_cons, List.length_nil] at h1 h2 ⊢
      nlinarith
  | pre, [rf], ws => by
      rw [eJobs]
      have h1 := dJobs_len (fun i => tgt (i + 1)) (pre ++ [(rf, false)]) [] ws
      simp only [List.length_cons, List.length_nil] at h1 ⊢
      nlinarith
  | pre, [], ws => by simp [eJobs]

theorem copyJobs_len {n : ℕ} (tgt : ℕ → Fin n) (rws : List (Fin n)) :
    (copyJobs tgt rws).length = rws.length := by
  induction rws generalizing tgt with
  | nil => simp [copyJobs]
  | cons r rs ih => simp [copyJobs, ih]

end Size

section Size2

theorem sum_take_le (l : List ℕ) (r : ℕ) : (l.take r).sum ≤ l.sum := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih => cases r <;> simp [ih]

theorem Sprime_size_le (S : QStrategy) (r : ℕ) (hV : S.Valid) (hr : r < S.steps.length) :
    (Sprime S r).size ≤ 1000 * (S.size + 1) ^ 5 := by
  set st := S.stepAt r
  set L := Lof S r
  have hmem : st ∈ S.steps := by
    simp only [st, QStrategy.stepAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
    exact List.getElem_mem hr
  have hnd : st.outW.Nodup := (hV.2 st hmem).2
  have hL : st.outW.length = L := rfl
  have hstle : st.size ≤ (S.steps.map RoundStep.size).sum := List.le_sum_of_mem (List.mem_map_of_mem hmem)
  have hsz : S.size = S.inQ + S.wkQ + S.steps.length + (S.steps.map RoundStep.size).sum := rfl
  set X := S.size + 1
  have hX : 1 ≤ X := by omega
  have hLX : L ≤ X := by simp only [RoundStep.size] at hstle; omega
  have hcX : st.circ.length ≤ X := by
    simp only [RoundStep.size, Circuit.size] at hstle; omega
  have hrX : r + 1 ≤ X := by omega
  have hD := jobsCirc_len (jobsD L (hN S r) st.outW) (ancL L (hN S r)) (L + 1)
    (fun j hj => (jobsD_ctrl L (hN S r) st.outW hnd hL j hj).2.2.1)
  have hE := jobsCirc_len (jobsE L (hN S r) st.outW) (ancL L (hN S r)) (2 * L + 3)
    (fun j hj => (jobsE_ctrl L (hN S r) st.outW hnd hL j hj).2.2.1)
  have hDn : (jobsD L (hN S r) st.outW).length ≤ L * (2 * L) := by
    have := dJobs_len (Rw L (hN S r)) [] [] (wsL L (hN S r) st.outW)
    simpa [jobsD, wsL, hL] using this
  have hEn : (jobsE L (hN S r) st.outW).length ≤ (L + 1) + (L + 1) * (2 * L * L) := by
    have h1 := eJobs_len (Ow L (hN S r)) [] (rws L (hN S r)) (wsL L (hN S r) st.outW)
    have h2 := copyJobs_len (Ow L (hN S r)) (rws L (hN S r))
    simp only [jobsE, List.length_append, h2]
    simp only [rws, wsL, List.length_map, List.length_range, hL] at h1 ⊢
    omega
  have hfl : (flipCirc (n := S.N) st.inW).length ≤ 1 := by
    cases st.inW <;> simp [flipCirc]
  have hsum : (((S.steps.take r).map (liftStep (hN S r))).map RoundStep.size).sum ≤
      (S.steps.map RoundStep.size).sum := by
    rw [List.map_map]
    have : (RoundStep.size ∘ liftStep (hN S r)) = RoundStep.size := by
      funext t; simp [RoundStep.size, liftStep, liftCirc, Circuit.size]
    rw [this, List.map_take]
    exact sum_take_le _ _
  have hsize : (Sprime S r).size = S.inQ + (S.wkQ + (5 * L + 7)) + (r + 1) +
      ((((S.steps.take r).map (liftStep (hN S r))).map RoundStep.size).sum +
        (st.circ.length + (jobsCirc (jobsD L (hN S r) st.outW) (ancL L (hN S r))).length +
          st.circ.length + (flipCirc (n := S.N) st.inW).length +
          st.circ.length + (jobsCirc (jobsE L (hN S r) st.outW) (ancL L (hN S r))).length +
          (2 * L + 2))) := by
    simp only [QStrategy.size, Sprime, List.length_append, List.length_map, List.length_take,
      List.length_singleton, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, finalStep, RoundStep.size, finalCirc, Circuit.size,
      liftCirc, ows, List.length_range, List.length_nil, add_zero, zero_add]
    rw [show (QCircuit.adj st.circ).length = st.circ.length from QCircuit.adj_size st.circ]
    simp only [Nat.min_eq_left hr.le]
    rfl
  rw [hsize]
  have b1 : L * (2 * L) ≤ 2 * X ^ 2 := by nlinarith
  have b2 : 20 * (L + 1 + 1) ≤ 60 * X := by omega
  have bD : (jobsCirc (jobsD L (hN S r) st.outW) (ancL L (hN S r))).length ≤ 120 * X ^ 3 :=
    le_trans hD (by
      calc _ ≤ (2 * X ^ 2) * (60 * X) := Nat.mul_le_mul (hDn.trans b1) b2
        _ = 120 * X ^ 3 := by ring)
  have b3 : (L + 1) + (L + 1) * (2 * L * L) ≤ 6 * X ^ 3 := by
    have h1 : L + 1 ≤ 2 * X := by omega
    have h2 : (L + 1) * (2 * L * L) ≤ (2 * X) * (2 * X * X) := by
      apply Nat.mul_le_mul h1; apply Nat.mul_le_mul (by omega) hLX
    have h3 : 2 * X ≤ 2 * X ^ 3 := by
      have : X ≤ X ^ 3 := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ 3 := Nat.pow_le_pow_right hX (by norm_num)
      omega
    nlinarith
  have b4 : 20 * (2 * L + 3 + 1) ≤ 120 * X := by omega
  have bE : (jobsCirc (jobsE L (hN S r) st.outW) (ancL L (hN S r))).length ≤ 720 * X ^ 4 :=
    le_trans hE (by
      calc _ ≤ (6 * X ^ 3) * (120 * X) := Nat.mul_le_mul (hEn.trans b3) b4
        _ = 720 * X ^ 4 := by ring)
  have p1 : X ≤ X ^ 5 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 5 := Nat.pow_le_pow_right hX (by norm_num)
  have p3 : X ^ 3 ≤ X ^ 5 := Nat.pow_le_pow_right hX (by norm_num)
  have p4 : X ^ 4 ≤ X ^ 5 := Nat.pow_le_pow_right hX (by norm_num)
  have hq : S.inQ + S.wkQ ≤ X := by omega
  have hsumX : (S.steps.map RoundStep.size).sum ≤ X := by omega
  nlinarith

end Size2

section Assembly

theorem ows_nodup {N N' : ℕ} (L : ℕ) (h : N + (5 * L + 7) = N') : (ows L h).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro a ha b hb hab
  simp at ha hb
  have := fw_inj L h _ _ (by omega) (by omega) hab; omega

theorem Sprime_valid (S : QStrategy) (r : ℕ) (hV : S.Valid) :
    (Sprime S r).Valid := by
  refine ⟨?_, ?_⟩
  · have hh : S.wkQ + mOf S r = S.wkQ + mOf S r := rfl
    show ∑ z : Qubits (S.wkQ + mOf S r), ‖S.advice (fun i => z (Fin.castAdd _ i)) *
      (if ∀ j : Fin (mOf S r), z (Fin.natAdd S.wkQ j) = false then 1 else 0)‖ ^ 2 = 1
    rw [sum_split hh]
    rw [← hV.1]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.sum_eq_single (fun _ => false)]
    · have e1 : (fun i => (splitQ hh).symm (p, fun _ => false) (Fin.castAdd (mOf S r) i)) = p := by
        have := split_symm_e hh p (fun _ => false)
        funext i; exact congrFun this i
      have e2 : ∀ j : Fin (mOf S r), (splitQ hh).symm (p, fun _ => false) (Fin.natAdd S.wkQ j) = false := by
        intro j
        have := split_symm_f hh p (fun _ => false)
        exact congrFun this j
      rw [e1, if_pos e2]; simp
    · intro q _ hq
      have e2 : ¬ ∀ j : Fin (mOf S r), (splitQ hh).symm (p, q) (Fin.natAdd S.wkQ j) = false := by
        intro H; apply hq; funext j
        have := congrFun (split_symm_f hh p q) j
        rw [← this]; exact H j
      rw [if_neg e2]; simp
    · simp
  · have key : ∀ s ∈ (S.steps.take r).map (liftStep (hN S r)) ++ [finalStep S r],
        s.inW.Nodup ∧ s.outW.Nodup := by
      intro s hs'
      rw [List.mem_append, List.mem_map, List.mem_singleton] at hs'
      rcases hs' with ⟨t, ht, rfl⟩ | rfl
      · have := hV.2 t (List.mem_of_mem_take ht)
        exact ⟨this.1.map (eL _).injective, this.2.map (eL _).injective⟩
      · exact ⟨List.nodup_nil, ows_nodup _ _⟩
    exact key

noncomputable def Sfam (Cm : CommitmentScheme) (S : ℕ → QStrategy) (n : ℕ) : QStrategy :=
  if Cm.rounds n < (S n).steps.length then Sprime (S n) (Cm.rounds n) else S n

theorem Sfam_QPT (Cm : CommitmentScheme) (S : ℕ → QStrategy) (hS : IsQPT S) : IsQPT (Sfam Cm S) := by
  obtain ⟨hV, p, hp⟩ := hS
  refine ⟨fun n => ?_, ⟨Polynomial.C 1000 * (p + 1) ^ 5 + p, fun n => ?_⟩⟩
  · unfold Sfam; split_ifs with h
    · exact Sprime_valid _ _ (hV n)
    · exact hV n
  · have hpn := hp n
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_one]
    unfold Sfam; split_ifs with h
    · calc (Sprime (S n) (Cm.rounds n)).size ≤ 1000 * ((S n).size + 1) ^ 5 :=
          Sprime_size_le _ _ (hV n) h
        _ ≤ 1000 * (p.eval n + 1) ^ 5 := by gcongr
        _ ≤ _ := Nat.le_add_right _ _
    · exact hpn.trans (Nat.le_add_left _ _)

theorem reduction_proof (Cm : CommitmentScheme) (huo : Cm.HasUniqueOpenings)
    (S : ℕ → QStrategy) (hS : IsQPT S) :
    ∃ S' : ℕ → QStrategy, IsQPT S' ∧ ∀ n,
      sumBindingProb Cm (S n) n - 1 / 2 ≤ 4 * Real.sqrt (openBothProb Cm (S' n) n) := by
  refine ⟨Sfam Cm S, Sfam_QPT Cm S hS, fun n => ?_⟩
  have h1 := sum_bound Cm (S n) n (hS.1 n)
  have h2 : (avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
      ∑ o : (S n).Outs (Cm.rounds n), qval Cm (S n) n c (QStrategy.outList o)) ≤
      openBothProb Cm (Sfam Cm S n) n := by
    unfold Sfam; split_ifs with h
    · exact openBoth_Sprime_ge Cm n (S n) (hS.1 n) huo h
    · exact openBoth_short_ge Cm n (S n) (by omega)
  have h3 := Real.sqrt_le_sqrt h2
  have h4 : 0 ≤ Real.sqrt (openBothProb Cm (Sfam Cm S n) n) := Real.sqrt_nonneg _
  linarith

end Assembly

/-- If `μ` is negligible then so is `4 √|μ|`. -/
lemma negl_sqrt (μ : ℕ → ℝ) (h : CompNonlocal.Negligible μ) :
    CompNonlocal.Negligible (fun n => 4 * Real.sqrt |μ n|) := by
  intro p
  have h1 := h (p * p)
  have h2 : Filter.Tendsto (fun n : ℕ => 4 * Real.sqrt (|μ n| * |(p * p).eval (n : ℝ)|))
      Filter.atTop (nhds 0) := by
    have h3 : Filter.Tendsto (fun n : ℕ => |μ n| * |(p * p).eval (n : ℝ)|)
        Filter.atTop (nhds 0) := by
      have := h1.abs
      simpa [abs_mul] using this
    have := (h3.sqrt).const_mul 4
    simpa using this
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine h2.congr (fun n => ?_)
  simp only [Function.comp, Polynomial.eval_mul]
  rw [abs_mul, abs_mul, Real.sqrt_mul (abs_nonneg _), Real.sqrt_mul_self (abs_nonneg _),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.sqrt |μ n|)]
  ring_nf
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt |μ n| * 4)]
  ring

theorem lemma_4_proof (Cm : CommitmentScheme) (hppt : Cm.IsPPT) (hbit : Cm.IsBit)
    (huo : Cm.HasUniqueOpenings) (hoob : Cm.IsOpenOnceBinding) :
    Cm.IsSumBinding := by
  intro S hS
  obtain ⟨S', hS', hred⟩ := reduction_proof Cm huo S hS
  obtain ⟨μ, hμ, hle⟩ := hoob S' hS'
  refine ⟨fun n => 4 * Real.sqrt |μ n|, negl_sqrt μ hμ, fun n => ?_⟩
  have h1 := hred n
  have h2 : Real.sqrt (openBothProb Cm (S' n) n) ≤ Real.sqrt |μ n| :=
    Real.sqrt_le_sqrt ((hle n).trans (le_abs_self _))
  linarith
end NovyPQZK.Main

theorem solution (Cm : NovyPQZK.Main.CommitmentScheme) (hppt : Cm.IsPPT) (hbit : Cm.IsBit)
    (huo : Cm.HasUniqueOpenings) (hoob : Cm.IsOpenOnceBinding) :
    Cm.IsSumBinding :=
  NovyPQZK.Main.lemma_4_proof Cm hppt hbit huo hoob
