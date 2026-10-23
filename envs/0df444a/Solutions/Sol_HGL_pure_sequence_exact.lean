-- Prove2me | solution 1 for HGL.pure_sequence_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:51:12.189018+00:00
-- url     : https://prove2.me/submissions/6aa797d8-f141-4c48-bd52-84f9a2600e9a

import Mathlib
import Definitions.Def_HGL_alg
import Definitions.Def_HGL_tor

open HGL


theorem hgl84_cong {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∀ s t u v : S, EqvGen W.moves s t → EqvGen W.moves u v →
      EqvGen W.moves (s * u) (t * v) := by
  have hr : ∀ u s t : S, EqvGen W.moves s t → EqvGen W.moves (s * u) (t * u) := by
    intro u s t h
    induction h with
    | refl s => exact EqvGen.refl _
    | symm _ ih => exact EqvGen.symm ih
    | trans _ _ ih1 ih2 => exact EqvGen.trans ih1 ih2
    | step h => exact EqvGen.step (W.move_mul _ _ _ h)
  have hl : ∀ u s t : S, EqvGen W.moves s t → EqvGen W.moves (u * s) (u * t) := by
    intro u s t h
    induction h with
    | refl s => exact EqvGen.refl _
    | symm _ ih => exact EqvGen.symm ih
    | trans _ _ ih1 ih2 => exact EqvGen.trans ih1 ih2
    | step h => exact EqvGen.step (W.move_mul_left _ _ _ h)
  intro s t u v h1 h2
  exact EqvGen.trans (hr u s t h1) (hl t u v h2)

theorem hgl84_ker {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) (b : B) :
    b ∈ (W.cls.comp W.incl).ker ↔ EqvGen W.moves (W.incl b) 1 := by
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, W.cls_trivial]

theorem hgl84_sub {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∃ H : Subgroup B, ∀ b : B, b ∈ H ↔ EqvGen W.moves (W.incl b) 1 :=
  ⟨_, hgl84_ker W⟩

theorem hgl84_normal {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∀ H : Subgroup B, (∀ b : B, b ∈ H ↔ EqvGen W.moves (W.incl b) 1) → H.Normal := by
  intro H hH
  have : H = (W.cls.comp W.incl).ker := by
    ext b; rw [hH, hgl84_ker]
  rw [this]; infer_instance

theorem hgl84_class {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∀ c : Cl, ∃ s : S, W.cls s = c ∧ c⁻¹ = W.cls (W.mirror s) := by
  intro c
  obtain ⟨s, rfl⟩ := W.cls_surj c
  exact ⟨s, rfl, eq_inv_of_mul_eq_one_right (W.cls_mirror s) |>.symm⟩

theorem hgl84_surj {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) : ∀ c : Cl, ∃ b : B, W.cls (W.incl b) = c := by
  intro c
  obtain ⟨s, rfl⟩ := W.cls_surj c
  obtain ⟨b, hb⟩ := W.to_braid s
  exact ⟨b, (W.cls_moves _ _ hb).symm⟩

theorem hgl84_quot {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∃ e : B →* Cl, (∀ b : B, e b = W.cls (W.incl b)) ∧
      (∀ c : Cl, ∃ b : B, e b = c) ∧
      (∀ b : B, e b = 1 ↔ EqvGen W.moves (W.incl b) 1) :=
  ⟨W.cls.comp W.incl, fun _ => rfl, hgl84_surj W, fun b => W.cls_trivial _⟩

theorem hgl84_pure {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    (∀ p : Equiv.Perm (Fin n), ∃ c : Cl, W.permCl c = p) ∧
    (∀ c : Cl, W.permCl c = 1 ↔ ∃ b : B, W.perm b = 1 ∧ W.cls (W.incl b) = c) := by
  refine ⟨fun p => ?_, fun c => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨b, rfl⟩ := W.perm_surj p
    exact ⟨_, W.permCl_compat b⟩
  · obtain ⟨b, rfl⟩ := hgl84_surj W c
    exact ⟨b, by rw [← W.permCl_compat]; exact h, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    rw [W.permCl_compat, hb]

/-! Counterexample to the presentation theorems: `Cl = S₃`, target `ZMod 4`. -/

abbrev P3 := Equiv.Perm (Fin 3)

theorem hgl84_eqv_eq {s t : P3} (h : EqvGen (fun x y : P3 => x = y) s t) : s = t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | step h => exact h

def hgl84_gs : Fin (3 - 1) → P3 := ![Equiv.swap 0 1, Equiv.swap 1 2]

theorem hgl84_enum : ∀ x : P3, x ∈ [1, Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 1 2 * Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1] := by decide

theorem hgl84_span : Subgroup.closure (Set.range hgl84_gs ∪ Set.range (fun r : Fin (2 * 0) => r.elim0 : Fin (2 * 0) → P3)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have ha : Equiv.swap (0 : Fin 3) 1 ∈ Subgroup.closure (Set.range hgl84_gs ∪ Set.range (fun r : Fin (2 * 0) => r.elim0 : Fin (2 * 0) → P3)) :=
    Subgroup.subset_closure (Or.inl ⟨0, rfl⟩)
  have hb : Equiv.swap (1 : Fin 3) 2 ∈ Subgroup.closure (Set.range hgl84_gs ∪ Set.range (fun r : Fin (2 * 0) => r.elim0 : Fin (2 * 0) → P3)) :=
    Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
  have hx : x ∈ [1, Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 2,
      Equiv.swap 1 2 * Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1] := hgl84_enum x
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact ha
  · exact hb
  · exact Subgroup.mul_mem _ ha hb
  · exact Subgroup.mul_mem _ hb ha
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha

def hgl84_W : LinkHomotopyWorld 3 0 P3 P3 P3 where
  hn := by norm_num
  moves := fun x y => x = y
  move_mul := fun _ _ _ h => by rw [h]
  move_mul_left := fun _ _ _ h => by rw [h]
  incl := MonoidHom.id _
  to_braid := fun s => ⟨s, EqvGen.refl _⟩
  mirror := fun s => s⁻¹
  mirror_compat := fun s => by rw [mul_inv_cancel]; exact EqvGen.refl _
  cls := MonoidHom.id _
  cls_moves := fun _ _ h => hgl84_eqv_eq h
  cls_trivial := fun s => ⟨fun h => by rw [show s = 1 from h]; exact EqvGen.refl _, fun h => hgl84_eqv_eq h⟩
  cls_surj := fun c => ⟨c, rfl⟩
  cls_mirror := fun s => mul_inv_cancel s
  gen_sigma := hgl84_gs
  gen_a := fun r => r.elim0
  gen_span := hgl84_span
  perm := MonoidHom.id _
  perm_surj := fun p => ⟨p, rfl⟩
  permCl := MonoidHom.id _
  permCl_compat := fun _ => rfl

abbrev Z4 := Multiplicative (ZMod 4)

theorem hgl84_comm_one {G : Type*} [CommGroup G] (x y : G) : x * y * x⁻¹ * y⁻¹ = 1 := by
  rw [mul_right_comm x y, mul_inv_cancel, one_mul, mul_inv_cancel]

theorem hgl84_pres :
    SatisfiesPresentation (n := 3) (g := 0) (by norm_num) (fun _ => (Multiplicative.ofAdd 1 : Z4))
      (fun r => r.elim0) := by
  refine ⟨fun _ _ _ => hgl84_comm_one _ _, fun _ _ _ => mul_comm _ _, fun _ _ => rfl, ?_,
    fun r => r.elim0, fun r => absurd r.2 (by norm_num), fun r => r.elim0⟩
  decide

theorem hgl84_punct :
    SatisfiesPuncturedPresentation (n := 3) (g := 0) (by norm_num) (fun _ => (Multiplicative.ofAdd 1 : Z4))
      (fun r => r.elim0) := by
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := hgl84_pres
  exact ⟨h1, h2, h3, h5, h6, h7⟩

theorem hgl84_nohom : ¬ ∃ f : P3 →* Z4, f (Equiv.swap 0 1) = Multiplicative.ofAdd 1 := by
  rintro ⟨f, hf⟩
  have h : f (Equiv.swap 0 1 * Equiv.swap 0 1) = 1 := by
    rw [Equiv.swap_mul_self, map_one]
  rw [map_mul, hf] at h
  revert h; decide


/-!  Milestone 6 (Proposition 3.8): the short exact sequence from the pure
link-homotopy classes to the full class group and onto the symmetric
group. The permutation map of the class group is surjective - every
permutation is realized by a braid - and its kernel is exactly the set of
classes of pure braids, so the sequence of Proposition 3.8 is exact. -/
theorem solution {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    (∀ p : Equiv.Perm (Fin n), ∃ c : Cl, W.permCl c = p) ∧
    (∀ c : Cl, W.permCl c = 1 ↔ ∃ b : B, W.perm b = 1 ∧ W.cls (W.incl b) = c) := by
  exact hgl84_pure W


