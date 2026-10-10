-- Prove2me | solution 1 for OAI.ThompsonNonamenability.thompson_F_nonamenable_composition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T21:51:26.143635+00:00
-- url     : https://prove2.me/submissions/376c28c7-303a-4958-be44-19564c04744f

import Mathlib
import Definitions.Def_ThompsonNonamenability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_CannonFloydParry
import Theorems.Thm_ThompsonAmenability_not_isAmenable_F
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_Garrido_isAmenable_tfae

/-! OpenAI's comparator form of "Thompson's group F is nonamenable", reduced to the published
`ThompsonAmenability.not_isAmenable_F` (proved from OpenAI's openai/math family 248).
OpenAI's `F` is in bijection with `CannonFloydParry.F`; the group structure is transported. -/

namespace TNReduction

open OAI.ThompsonNonamenability
open scoped Pointwise

/-- Amenability transfers backwards along a group isomorphism. -/
theorem isAmenable_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : H ≃* G)
    (hG : Garrido.IsAmenable G) : Garrido.IsAmenable H := by
  obtain ⟨m, ⟨h0, hadd⟩, h1, hinv⟩ := hG
  refine ⟨fun s => m (e '' s), ⟨by simpa using h0, ?_⟩, ?_, ?_⟩
  · intro s t hst
    simp only [Set.image_union]
    exact hadd _ _ ((Set.disjoint_image_iff e.injective).2 hst)
  · simpa [Set.image_univ_of_surjective e.surjective] using h1
  · intro g s
    show m (e '' (g • s)) = m (e '' s)
    rw [show e '' (g • s) = e g • (e '' s) from Set.image_smul_distrib e g s]
    exact hinv _ _

/-- An element of OpenAI's `F` as an order isomorphism of the unit interval. -/
noncomputable def toOI (g : F) : CannonFloydParry.UI ≃o CannonFloydParry.UI :=
  StrictMono.orderIsoOfSurjective (fun x => g.val x) g.2.1
    (fun y => ⟨g.val.toHomeomorph.symm y, g.val.toHomeomorph.apply_symm_apply y⟩)

theorem toOI_apply (g : F) (x : CannonFloydParry.UI) : toOI g x = g.val x := rfl

theorem isThompson_toOI (g : F) : CannonFloydParry.IsThompson (toOI g) := by
  classical
  let w : DyadicPLWitness g.val := Classical.choice g.2.2
  refine ⟨Finset.univ.image (fun i => (w.knots i : ℝ)), ?_, ?_⟩
  · intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k, n, hk⟩ := w.dyadic i
    exact ⟨k, n, hk⟩
  · intro x y hxy hB
    have hx0 := x.2.1
    have hy1 := y.2.2
    let mid : CannonFloydParry.UI :=
      ⟨((x : ℝ) + y) / 2, by constructor <;> linarith⟩
    have hmx : (x : ℝ) < mid := by show (x : ℝ) < ((x : ℝ) + y) / 2; linarith
    have hmy : (mid : ℝ) < y := by show ((x : ℝ) + y) / 2 < y; linarith
    obtain ⟨i, hi1, hi2⟩ := w.cover mid
    have hi1' : (w.knots i.castSucc : ℝ) ≤ mid := hi1
    have hi2' : (mid : ℝ) ≤ w.knots i.succ := hi2
    have hkx : (w.knots i.castSucc : ℝ) ≤ x := by
      by_contra h
      push Not at h
      have hmem : (w.knots i.castSucc : ℝ) ∈ Set.Ioo (x : ℝ) y ∩
          ((Finset.univ.image (fun i => (w.knots i : ℝ)) : Finset ℝ) : Set ℝ) :=
        ⟨⟨h, lt_of_le_of_lt hi1' hmy⟩, by simp⟩
      rw [hB] at hmem
      exact hmem
    have hky : (y : ℝ) ≤ w.knots i.succ := by
      by_contra h
      push Not at h
      have hmem : (w.knots i.succ : ℝ) ∈ Set.Ioo (x : ℝ) y ∩
          ((Finset.univ.image (fun i => (w.knots i : ℝ)) : Finset ℝ) : Set ℝ) :=
        ⟨⟨lt_of_lt_of_le hmx hi2', h⟩, by simp⟩
      rw [hB] at hmem
      exact hmem
    refine ⟨w.exponent i,
      (g.val (w.knots i.castSucc) : ℝ) - 2 ^ w.exponent i * (w.knots i.castSucc : ℝ), ?_⟩
    intro z hz
    have h := w.affine i z (le_trans hkx hz.1) (le_trans hz.2 hky)
    rw [toOI_apply, h]
    ring

theorem toOI_injective : Function.Injective toOI := by
  intro g h hgh
  obtain ⟨⟨eg⟩, _⟩ := g
  obtain ⟨⟨eh⟩, _⟩ := h
  have : eg = eh := by
    ext x
    exact congrArg Subtype.val (DFunLike.congr_fun hgh x)
  subst this
  rfl

/-- The breakpoints of a Thompson map lie on a common dyadic grid. -/
theorem exists_grid (B : Finset ℝ) (hB : ∀ b ∈ B, CannonFloydParry.IsDyadic b) :
    ∃ N : ℕ, ∀ b ∈ B, ∃ m : ℤ, b = (m : ℝ) / 2 ^ N := by
  classical
  induction B using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨N, hN⟩ := ih (fun b hb => hB b (Finset.mem_insert_of_mem hb))
    obtain ⟨m, k, hk⟩ := hB a (Finset.mem_insert_self a s)
    have regrid : ∀ (m : ℤ) (k M : ℕ), k ≤ M →
        (m : ℝ) / 2 ^ k = ((m * 2 ^ (M - k) : ℤ) : ℝ) / 2 ^ M := by
      intro m k M hkM
      have h2 : (2 : ℝ) ^ M = 2 ^ k * 2 ^ (M - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hkM]
      rw [h2]
      push_cast
      field_simp
    refine ⟨max N k, fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact ⟨_, hk.trans (regrid m k _ (le_max_right _ _))⟩
    · obtain ⟨m', hm'⟩ := hN b hb
      exact ⟨_, hm'.trans (regrid m' N _ (le_max_left _ _))⟩

section ofThompson

variable (f : CannonFloydParry.UI ≃o CannonFloydParry.UI)

/-- The homeomorphism underlying an order isomorphism of the unit interval. -/
noncomputable def ihOf : IntervalHomeomorph := ⟨f.toHomeomorph⟩

theorem ihOf_apply (x : UnitInterval) : ihOf f x = f x := rfl

variable {f}

theorem grid_knot_mem (N : ℕ) (i : Fin (2 ^ N + 1)) :
    ((i : ℕ) : ℝ) / 2 ^ N ∈ Set.Icc (0 : ℝ) 1 := by
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  have hi : ((i : ℕ) : ℝ) ≤ 2 ^ N := by exact_mod_cast Nat.lt_succ_iff.1 i.2
  constructor
  · positivity
  · rw [div_le_one hp]; exact hi

/-- Each grid cell `[i/2^N, (i+1)/2^N]` contains no breakpoint in its interior. -/
theorem cell_affine (hf : CannonFloydParry.IsThompson f) :
    ∃ N : ℕ, ∀ i : Fin (2 ^ N), ∃ (n : ℤ) (c : ℝ), ∀ z : CannonFloydParry.UI,
      (z : ℝ) ∈ Set.Icc (((i : ℕ) : ℝ) / 2 ^ N) ((((i : ℕ) + 1 : ℕ) : ℝ) / 2 ^ N) →
        (f z : ℝ) = 2 ^ n * (z : ℝ) + c := by
  obtain ⟨B, hBd, hB⟩ := hf
  obtain ⟨N, hN⟩ := exists_grid B hBd
  refine ⟨N, fun i => ?_⟩
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  let x : CannonFloydParry.UI := ⟨_, grid_knot_mem N i.castSucc⟩
  let y : CannonFloydParry.UI := ⟨_, grid_knot_mem N i.succ⟩
  have hxy : (x : ℝ) < y := by
    show ((i.castSucc : ℕ) : ℝ) / 2 ^ N < ((i.succ : ℕ) : ℝ) / 2 ^ N
    rw [div_lt_div_iff_of_pos_right hp]
    simp
  have hempty : Set.Ioo (x : ℝ) y ∩ (B : Set ℝ) = ∅ := by
    ext b
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro ⟨h1, h2⟩ hb
    obtain ⟨m, rfl⟩ := hN b hb
    change ((i.castSucc : ℕ) : ℝ) / 2 ^ N < (m : ℝ) / 2 ^ N at h1
    change (m : ℝ) / 2 ^ N < ((i.succ : ℕ) : ℝ) / 2 ^ N at h2
    rw [div_lt_div_iff_of_pos_right hp] at h1 h2
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h1' : ((i : ℕ) : ℤ) < m := by exact_mod_cast h1
    have h2' : m < ((i : ℕ) : ℤ) + 1 := by exact_mod_cast h2
    omega
  obtain ⟨n, c, hc⟩ := hB x y hxy hempty
  exact ⟨n, c, fun z hz => hc z (by simpa [x, y] using hz)⟩

/-- A Thompson order isomorphism has OpenAI's dyadic piecewise-linear pieces. -/
theorem hasDyadicPLPieces (hf : CannonFloydParry.IsThompson f) :
    HasDyadicPLPieces (ihOf f) := by
  classical
  obtain ⟨N, hN⟩ := cell_affine hf
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  let knots : Fin (2 ^ N + 1) → UnitInterval := fun i => ⟨_, grid_knot_mem N i⟩
  have knots_val : ∀ i, (knots i : ℝ) = ((i : ℕ) : ℝ) / 2 ^ N := fun i => rfl
  refine ⟨{ pieceCount := 2 ^ N
            positive := by positivity
            knots := knots
            strictMono_knots := ?_
            first := ?_
            last := ?_
            dyadic := fun i => ⟨(i : ℕ), N, by rw [knots_val]; push_cast; rfl⟩
            cover := ?_
            exponent := fun i => Classical.choose (hN i)
            affine := ?_ }⟩
  · intro a b hab
    show (knots a : ℝ) < knots b
    rw [knots_val, knots_val, div_lt_div_iff_of_pos_right hp]
    exact_mod_cast hab
  · apply Subtype.ext
    show ((0 : ℕ) : ℝ) / 2 ^ N = 0
    simp
  · apply Subtype.ext
    show (((2 ^ N : ℕ)) : ℝ) / 2 ^ N = 1
    push_cast
    exact div_self hp.ne'
  · intro x
    have hx0 := x.2.1
    have hx1 := x.2.2
    have hN1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
    let j := min (⌊(x : ℝ) * (2 : ℝ) ^ N⌋₊) (2 ^ N - 1)
    have hj : j < 2 ^ N := lt_of_le_of_lt (min_le_right _ _) (by omega)
    refine ⟨⟨j, hj⟩, ?_, ?_⟩
    · show (knots _ : ℝ) ≤ x
      rw [knots_val, div_le_iff₀ hp]
      have h1 : (j : ℝ) ≤ ⌊(x : ℝ) * (2 : ℝ) ^ N⌋₊ := Nat.cast_le.2 (min_le_left _ _)
      have h2 : (⌊(x : ℝ) * 2 ^ N⌋₊ : ℝ) ≤ (x : ℝ) * 2 ^ N :=
        Nat.floor_le (by positivity)
      simp only [Fin.val_castSucc]
      linarith
    · show (x : ℝ) ≤ knots _
      rw [knots_val, le_div_iff₀ hp]
      simp only [Fin.val_succ]
      rcases le_total (⌊(x : ℝ) * 2 ^ N⌋₊) (2 ^ N - 1) with h | h
      · have hj' : j = ⌊(x : ℝ) * 2 ^ N⌋₊ := min_eq_left h
        rw [hj']
        push_cast
        exact (Nat.lt_floor_add_one _).le
      · have hj' : j = 2 ^ N - 1 := min_eq_right h
        have : ((j + 1 : ℕ) : ℝ) = 2 ^ N := by
          rw [hj', Nat.sub_add_cancel hN1]; push_cast; rfl
        rw [this]
        nlinarith
  · intro i x hx1 hx2
    obtain ⟨c, hc⟩ := Classical.choose_spec (hN i)
    have hk : (knots i.castSucc : ℝ) = ((i : ℕ) : ℝ) / 2 ^ N := by
      rw [knots_val]; rfl
    have hk' : (knots i.succ : ℝ) = (((i : ℕ) + 1 : ℕ) : ℝ) / 2 ^ N := by
      rw [knots_val]; rfl
    have hx1' : (knots i.castSucc : ℝ) ≤ x := hx1
    have hx2' : (x : ℝ) ≤ knots i.succ := hx2
    have ha := hc x ⟨hk ▸ hx1', hk' ▸ hx2'⟩
    have hb := hc (knots i.castSucc) ⟨le_of_eq hk.symm, by
      rw [div_le_div_iff_of_pos_right hp]; simp only [Fin.val_castSucc]; push_cast; linarith⟩
    rw [ihOf_apply, ihOf_apply, ha, hb]
    ring

/-- The element of OpenAI's `F` given by a Thompson order isomorphism. -/
noncomputable def ofThompson (hf : CannonFloydParry.IsThompson f) : F :=
  ⟨ihOf f, f.strictMono, hasDyadicPLPieces hf⟩

theorem toOI_ofThompson (hf : CannonFloydParry.IsThompson f) : toOI (ofThompson hf) = f := by
  ext x
  rfl

end ofThompson

/-- OpenAI's `F` is in bijection with `CannonFloydParry.F`. -/
noncomputable def equivF : F ≃ CannonFloydParry.F :=
  Equiv.ofBijective
    (fun g => ⟨toOI g, CannonFloydParry.mem_F_iff_isThompson.2 (isThompson_toOI g)⟩)
    ⟨fun g h hgh => toOI_injective (congrArg Subtype.val hgh), fun f => by
      obtain ⟨f, hf⟩ := f
      have ht := CannonFloydParry.mem_F_iff_isThompson.1 hf
      exact ⟨ofThompson ht, Subtype.ext (toOI_ofThompson ht)⟩⟩

theorem thompson_F_nonamenable_of_cfp :
    ∃ group : Group F, letI := group;
      (∀ (h g : F) (x : UnitInterval),
        (h * g).val.toHomeomorph x = h.val.toHomeomorph (g.val.toHomeomorph x)) ∧
      ¬ Nonempty (InvariantMean F) := by
  let _ : Group F := equivF.group
  refine ⟨equivF.group, ?_, ?_⟩
  · intro h g x
    have hmul : equivF (h * g) = equivF h * equivF g := equivF.apply_symm_apply _
    have := congrArg (fun k : CannonFloydParry.F =>
      ((k : CannonFloydParry.UI ≃o CannonFloydParry.UI) x)) hmul
    exact this
  · rintro ⟨M⟩
    have hmean : Garrido.HasInvariantMean F := by
      refine ⟨M.toLinearMap, M.positive, fun f hf => ?_, fun g f => ?_⟩
      · have : f = 1 := by
          apply lp.ext
          funext x
          simpa using hf x
        rw [this]
        exact M.normalized
      · have : Garrido.lshift g f = leftPull g⁻¹ f := by
          apply lp.ext
          funext x
          simp [leftPull, Garrido.lshift]
        rw [this]
        exact M.left_invariant _ _
    have hF : Garrido.IsAmenable F := ((Garrido.isAmenable_tfae F).out 0 1).2 hmean
    exact ThompsonAmenability.not_isAmenable_F
      (isAmenable_of_mulEquiv equivF.mulEquiv.symm hF)

end TNReduction

open OAI.ThompsonNonamenability in
theorem solution :
    ∃ group : Group F, letI := group;
      (∀ (h g : F) (x : UnitInterval),
        (h * g).val.toHomeomorph x = h.val.toHomeomorph (g.val.toHomeomorph x)) ∧
      ¬ Nonempty (InvariantMean F) :=
  TNReduction.thompson_F_nonamenable_of_cfp
