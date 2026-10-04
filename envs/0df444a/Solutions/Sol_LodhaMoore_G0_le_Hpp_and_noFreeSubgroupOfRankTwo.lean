-- Prove2me | solution 1 for LodhaMoore.G0_le_Hpp_and_noFreeSubgroupOfRankTwo
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.874291+00:00
-- url     : https://prove2.me/submissions/55328ce0-721f-42e6-be7e-096a778a2f55

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_Chou_Classes
import Definitions.Def_Garrido_Amenability
import Theorems.Thm_Monod_noFreeSubgroupOfRankTwo_Hpp
section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

theorem ofReal_coe {f : ℝ → ℝ} (e : ℝ ≃ₜ ℝ) (he : ∀ t, e t = f t) (t : ℝ) :
    ofReal f (t : OnePoint ℝ) = ((f t : ℝ) : OnePoint ℝ) := by
  have h : ∃ E : OnePoint ℝ ≃ₜ OnePoint ℝ, ∀ t : ℝ, E t = ((f t : ℝ) : OnePoint ℝ) :=
    ⟨e.onePointCongr, fun t => by rw [Homeomorph.onePointCongr_apply, OnePoint.map_some, he]⟩
  unfold ofReal
  rw [dif_pos h]
  exact h.choose_spec t

theorem aFun_strictMono : StrictMono aFun := fun x y h => by unfold aFun; linarith

theorem aFun_surjective : Function.Surjective aFun := fun u => ⟨u - 1, by unfold aFun; ring⟩

theorem bFun_strictMono : StrictMono bFun := by
  intro x y hxy
  unfold bFun
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 <;> try linarith
  all_goals first
    | (rw [lt_div_iff₀ (by linarith)]; nlinarith)
    | (rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith)
    | (have : 1 / y < 1 / x := one_div_lt_one_div_of_lt (by linarith) hxy; linarith)
    | (have : 1 / y < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
       have : x / (1 - x) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
       linarith)
    | (have : x / (1 - x) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
       linarith)
    | (have : 1 / x ≥ 1 := by rw [ge_iff_le, le_div_iff₀ (by linarith)]; linarith
       linarith)

theorem bFun_surjective : Function.Surjective bFun := by
  intro u
  unfold bFun
  by_cases h0 : u ≤ 0
  · exact ⟨u, by simp [h0]⟩
  by_cases h1 : u ≤ 1
  · refine ⟨u / (1 + u), ?_⟩
    have hp : 0 < 1 + u := by linarith
    have hpos : ¬ u / (1 + u) ≤ 0 := not_le.mpr (div_pos (by linarith) hp)
    have hh : u / (1 + u) ≤ 1 / 2 := by rw [div_le_iff₀ hp]; linarith
    simp only [hpos, hh, if_false, if_true]
    field_simp
    ring
  by_cases h2 : u ≤ 2
  · refine ⟨1 / (3 - u), ?_⟩
    have hp : 0 < 3 - u := by linarith
    have hpos : ¬ 1 / (3 - u) ≤ 0 := not_le.mpr (div_pos one_pos hp)
    have hh : ¬ 1 / (3 - u) ≤ 1 / 2 := by
      rw [not_le, div_lt_div_iff₀ two_pos hp]; linarith
    have hh1 : 1 / (3 - u) ≤ 1 := by rw [div_le_iff₀ hp]; linarith
    simp only [hpos, hh, hh1, if_false, if_true]
    field_simp
    ring
  · refine ⟨u - 1, ?_⟩
    have a1 : ¬ u - 1 ≤ 0 := by linarith
    have a2 : ¬ u - 1 ≤ 1 / 2 := by linarith
    have a3 : ¬ u - 1 ≤ 1 := by linarith
    simp only [a1, a2, a3, if_false]
    ring

theorem cFun_strictMono : StrictMono cFun := by
  intro x y hxy
  unfold cFun
  split_ifs with h1 h2 h2 <;> try linarith
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · -- x ∈ [0,1], y ∉ [0,1], so y > 1
    have hy : 1 < y := by
      by_contra hc; exact h2 ⟨by linarith, by linarith⟩
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  · -- x ∉ [0,1], y ∈ [0,1], so x < 0
    have hx : x < 0 := by
      by_contra hc; exact h1 ⟨by linarith, by linarith⟩
    rw [lt_div_iff₀ (by linarith)]; nlinarith

theorem cFun_surjective : Function.Surjective cFun := by
  intro u
  unfold cFun
  by_cases h : 0 ≤ u ∧ u ≤ 1
  · refine ⟨u / (2 - u), ?_⟩
    have hp : 0 < 2 - u := by linarith
    have hh : 0 ≤ u / (2 - u) ∧ u / (2 - u) ≤ 1 :=
      ⟨div_nonneg h.1 hp.le, by rw [div_le_iff₀ hp]; linarith⟩
    rw [if_pos hh]
    field_simp
    ring
  · exact ⟨u, by rw [if_neg h]⟩

noncomputable def aHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective aFun aFun_strictMono aFun_surjective).toHomeomorph
noncomputable def bHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective bFun bFun_strictMono bFun_surjective).toHomeomorph
noncomputable def cHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective cFun cFun_strictMono cFun_surjective).toHomeomorph

theorem a_coe (t : ℝ) : a (t : OnePoint ℝ) = ((aFun t : ℝ) : OnePoint ℝ) := ofReal_coe aHom (fun _ => rfl) t
theorem b_coe (t : ℝ) : b (t : OnePoint ℝ) = ((bFun t : ℝ) : OnePoint ℝ) := ofReal_coe bHom (fun _ => rfl) t
theorem c_coe (t : ℝ) : c (t : OnePoint ℝ) = ((cFun t : ℝ) : OnePoint ℝ) := ofReal_coe cHom (fun _ => rfl) t

end LodhaMoore
end

section
/-! Shared definitions for the Carrière–Ghys argument (Monod C9, `not_isAmenableRel_mob`). -/

namespace Monod.Dev.CG

open Matrix

variable {A : Subring ℝ}

end Monod.Dev.CG
end

section
/-! A4 of the Carrière–Ghys argument: for `|t| < 2`, the elliptic Möbius map `a_t : x ↦ t - 1/x`
preserves the finite measure `dx / (x² - t x + 1)` on `P¹`, which has the same null sets as
`volP1`; so `a_t` is conservative and every a.e. wandering set for `a_t` is null. -/

namespace Monod.Dev.CG.A4

open MeasureTheory Matrix OnePoint Set Filter

variable {A : Subring ℝ}

/-! ### The Möbius action of `ell t` -/

/-! ### The invariant weight `w(x) = 1 / (x² - τ x + 1)` -/

/-! ### Change of variables for `x ↦ τ - 1/x` -/

/-! ### Transport to `P¹` -/

end Monod.Dev.CG.A4

namespace Monod.Dev.CG

open MeasureTheory Matrix

end Monod.Dev.CG
end

section
namespace Monod.Dev.CG.A6

open Polynomial

end Monod.Dev.CG.A6

namespace Monod.Dev.CG

open Polynomial

end Monod.Dev.CG
end

section
/-! A5 + A7 of the Carrière–Ghys argument: the ping-pong partition of `SL(2, A)`. -/

namespace Monod.Dev.CG.A57

open Matrix

section PingPong

variable {K : Type} [NormedField K]

variable {E G : SpecialLinearGroup (Fin 2) K}

end PingPong

section Retraction

variable {A : Subring ℝ} (t : A)

end Retraction

end Monod.Dev.CG.A57

namespace Monod.Dev.CG

open Matrix

end Monod.Dev.CG
end

section
/-! # A8: the core of the Carrière–Ghys argument

A left invariant mean `P` on the orbit relation of `SL(2, A)` gives `u = P f_S`, where `f_S` is
the indicator of the pairs `(x, s x)` with `s ∈ S`.  Freeness off a countable set and the
ping-pong properties of `S` give `u + u ∘ b + u ∘ b² ≤ 1` and `1 ≤ u + u ∘ a^m` a.e.; the second
makes `{u < 1/2}` wandering for `a`, hence null, and the first is then contradictory. -/

namespace Monod.Dev.CG.A8

open Monod OnePoint Filter Topology Set MeasureTheory

variable {A : Subring ℝ}

/-! ### Möbius maps (copied from `DynBasic`) -/

/-! ### Measurability on `P¹ × P¹` -/

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

attribute [local instance] secondCountable_P1

theorem countable_SL (A : Subring ℝ) [Countable A] :
    Countable (Matrix.SpecialLinearGroup (Fin 2) A) :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → A // Matrix.det M = 1})

attribute [local instance] countable_SL

section Bdd

variable {X : Type*} [MeasurableSpace X]

end Bdd

/-! ### The global partial transformations `φ_g` -/

/-! ### Null sets of `volP1` -/

/-! ### Freeness off a countable set -/

/-! ### The two pointwise inequalities -/

end Monod.Dev.CG.A8

namespace Monod.Dev.CG

open MeasureTheory Matrix

end Monod.Dev.CG
end

section
/-! # Group S2: statements 1, 3, 6, 7, 8, 10 of the Lodha–Moore development -/

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set

/-! ### Möbius maps over `⊤ : Subring ℝ` -/

/-- The real entries of a matrix of `SL(2, A)`. -/
noncomputable abbrev ent {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    ℝ := ((g i j : A) : ℝ)

lemma slToGL_apply {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    (slToGL A g : GL (Fin 2) ℝ) i j = ent g i j := by
  simp [slToGL]

lemma mob_coe {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (t : ℝ) :
    mob g (t : OnePoint ℝ) = if ent g 1 0 * t + ent g 1 1 = 0 then ∞ else
      (((ent g 0 0 * t + ent g 0 1) / (ent g 1 0 * t + ent g 1 1) : ℝ) : OnePoint ℝ) := by
  unfold mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply]

lemma mob_infty {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    mob g ∞ = if ent g 1 0 = 0 then ∞ else ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ) := by
  unfold mob
  rw [OnePoint.smul_infty_eq_ite]
  simp only [slToGL_apply]

lemma mob_one {A : Subring ℝ} (x : OnePoint ℝ) :
    mob (1 : Matrix.SpecialLinearGroup (Fin 2) A) x = x := by
  unfold mob
  rw [map_one, one_smul]

/-- A matrix of `SL(2, ℝ)` (over `⊤ : Subring ℝ`) from its real entries. -/
noncomputable def mk2 (p q r s : ℝ) (h : p * s - q * r = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) :=
  ⟨!![⟨p, trivial⟩, ⟨q, trivial⟩; ⟨r, trivial⟩, ⟨s, trivial⟩], by
    rw [Matrix.det_fin_two_of]
    ext
    simpa using h⟩

@[simp] lemma ent_mk2_00 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 0 = p := rfl
@[simp] lemma ent_mk2_01 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 1 = q := rfl
@[simp] lemma ent_mk2_10 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 0 = r := rfl
@[simp] lemma ent_mk2_11 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 1 = s := rfl

lemma mob_mk2_coe (p q r s : ℝ) (h) (t : ℝ) (ht : r * t + s ≠ 0) :
    mob (mk2 p q r s h) (t : OnePoint ℝ) = (((p * t + q) / (r * t + s) : ℝ) : OnePoint ℝ) := by
  rw [mob_coe, if_neg (by simpa using ht)]
  simp

lemma mob_mk2_infty (p q r s : ℝ) (h) (hr : r = 0) : mob (mk2 p q r s h) ∞ = ∞ := by
  rw [mob_infty, if_pos (by simpa using hr)]

/-! ### Statement 1: `G₀ ≤ H` -/

/-- A homeomorphism of `P¹` that maps `ℝ` onto `ℝ` fixes `∞`. -/
lemma ofReal_infty {f : ℝ → ℝ} (e : ℝ ≃ₜ ℝ) (he : ∀ t, e t = f t) :
    ofReal f ∞ = ∞ := by
  by_contra hne
  obtain ⟨s, hs⟩ := OnePoint.ne_infty_iff_exists.1 hne
  have h1 : ofReal f ((e.symm s : ℝ) : OnePoint ℝ) = (s : OnePoint ℝ) := by
    rw [ofReal_coe e he, ← he, Homeomorph.apply_symm_apply]
  rw [hs] at h1
  exact OnePoint.coe_ne_infty _ ((ofReal f).injective h1)

lemma a_infty : a ∞ = ∞ := ofReal_infty aHom (fun _ => rfl)
lemma b_infty : b ∞ = ∞ := ofReal_infty bHom (fun _ => rfl)
lemma c_infty : c ∞ = ∞ := ofReal_infty cHom (fun _ => rfl)

/-- A property holding at the points of an open set `U ⊆ ℝ` holds near each point of `U`. -/
lemma eventually_of_open {U : Set ℝ} (hU : IsOpen U) {t : ℝ} (ht : t ∈ U)
    {P : OnePoint ℝ → Prop} (h : ∀ s ∈ U, P (s : OnePoint ℝ)) :
    ∀ᶠ y in 𝓝 (t : OnePoint ℝ), P y := by
  have hopen : IsOpen (((↑) : ℝ → OnePoint ℝ) '' U) := OnePoint.isOpen_image_coe.2 hU
  filter_upwards [hopen.mem_nhds ⟨t, ht, rfl⟩]
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

/-- `t ↦ t + 1`. -/
noncomputable def mTrans : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) :=
  mk2 1 1 0 1 (by norm_num)

lemma a_eq_mob (y : OnePoint ℝ) : a y = mob mTrans y := by
  cases y with
  | infty => rw [a_infty, mTrans, mob_mk2_infty _ _ _ _ _ rfl]
  | coe t =>
    rw [a_coe, mTrans, mob_mk2_coe _ _ _ _ _ _ (by norm_num)]
    congr 1; simp [aFun]

lemma a_piecewise : IsPiecewiseProjOn ⊤ Set.univ a :=
  ⟨∅, by simp, fun x _ => ⟨mTrans, Eventually.of_forall a_eq_mob⟩⟩

lemma b_piecewise : IsPiecewiseProjOn ⊤ Set.univ b := by
  classical
  refine ⟨{((0 : ℝ) : OnePoint ℝ), ((1 / 2 : ℝ) : OnePoint ℝ), ((1 : ℝ) : OnePoint ℝ), ∞},
    by simp, fun x hx => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨h0, h12, h1, hinf⟩ := hx
  cases x with
  | infty => exact absurd rfl hinf
  | coe t =>
    have h0 : t ≠ 0 := fun h => h0 (by rw [h])
    have h12 : t ≠ 1 / 2 := fun h => h12 (by rw [h])
    have h1 : t ≠ 1 := fun h => h1 (by rw [h])
    rcases lt_or_gt_of_ne h0 with ht0 | ht0
    · refine ⟨1, eventually_of_open isOpen_Iio (show t ∈ Iio 0 from ht0) fun s hs => ?_⟩
      rw [mob_one, b_coe]
      simp only [mem_Iio] at hs
      simp [bFun, hs.le]
    rcases lt_or_gt_of_ne h12 with ht12 | ht12
    · refine ⟨mk2 1 0 (-1) 1 (by norm_num),
        eventually_of_open isOpen_Ioo (show t ∈ Ioo 0 (1 / 2) from ⟨ht0, ht12⟩) fun s hs => ?_⟩
      obtain ⟨hs0, hs1⟩ := hs
      rw [b_coe, mob_mk2_coe _ _ _ _ _ _ (by linarith)]
      congr 1
      simp only [bFun, not_le.2 hs0, hs1.le, if_true, if_false]
      ring
    rcases lt_or_gt_of_ne h1 with ht1 | ht1
    · refine ⟨mk2 3 (-1) 1 0 (by norm_num),
        eventually_of_open isOpen_Ioo (show t ∈ Ioo (1 / 2) 1 from ⟨ht12, ht1⟩) fun s hs => ?_⟩
      obtain ⟨hs0, hs1⟩ := hs
      rw [b_coe, mob_mk2_coe _ _ _ _ _ _ (by linarith)]
      congr 1
      have hs0' : ¬ s ≤ 0 := by linarith
      simp only [bFun, hs0', not_le.2 hs0, hs1.le, if_true, if_false]
      field_simp
      ring
    · refine ⟨mTrans, eventually_of_open isOpen_Ioi (show t ∈ Ioi 1 from ht1) fun s hs => ?_⟩
      simp only [mem_Ioi] at hs
      rw [b_coe, mTrans, mob_mk2_coe _ _ _ _ _ _ (by norm_num)]
      congr 1
      have a1 : ¬ s ≤ 0 := by linarith
      have a2 : ¬ s ≤ 1 / 2 := by linarith
      have a3 : ¬ s ≤ 1 := by linarith
      simp only [bFun, a1, a2, a3, if_false]
      ring

lemma c_piecewise : IsPiecewiseProjOn ⊤ Set.univ c := by
  classical
  refine ⟨{((0 : ℝ) : OnePoint ℝ), ((1 : ℝ) : OnePoint ℝ)}, by simp, fun x hx => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨h0, h1⟩ := hx
  set V : Set (OnePoint ℝ) := (((↑) : ℝ → OnePoint ℝ) '' Icc 0 1)ᶜ with hV
  have hVo : IsOpen V :=
    ((isCompact_Icc.image OnePoint.continuous_coe).isClosed).isOpen_compl
  have hVc : ∀ y ∈ V, c y = mob (1 : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) y := by
    intro y hy
    rw [mob_one]
    cases y with
    | infty => exact c_infty
    | coe s =>
      rw [c_coe]
      have : ¬ (0 ≤ s ∧ s ≤ 1) := fun h => hy ⟨s, h, rfl⟩
      simp [cFun, this]
  by_cases hxV : x ∈ V
  · exact ⟨1, Filter.mem_of_superset (hVo.mem_nhds hxV) hVc⟩
  · simp only [hV, mem_compl_iff, not_not, mem_image] at hxV
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hxV
    have ht0' : 0 < t := lt_of_le_of_ne ht0 (fun h => h0 (by rw [h]))
    have ht1' : t < 1 := lt_of_le_of_ne ht1 (fun h => h1 (by rw [h]))
    have hs2 : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
      field_simp
    refine ⟨mk2 (Real.sqrt 2) 0 (1 / Real.sqrt 2) (1 / Real.sqrt 2) (by rw [hs2]; ring),
      eventually_of_open isOpen_Ioo (show t ∈ Ioo 0 1 from ⟨ht0', ht1'⟩) fun s hs => ?_⟩
    obtain ⟨hs0, hs1⟩ := hs
    have hpos : 0 < 1 / Real.sqrt 2 * s + 1 / Real.sqrt 2 := by positivity
    rw [c_coe, mob_mk2_coe _ _ _ _ _ _ hpos.ne']
    congr 1
    simp only [cFun, hs0.le, hs1.le, and_self, if_true]
    have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [div_eq_div_iff (by positivity) hpos.ne']
    field_simp
    linear_combination (-(s + s^2)) * h22

lemma mem_Hpp_of {f : OnePoint ℝ ≃ₜ OnePoint ℝ} (hf : IsPiecewiseProjOn ⊤ Set.univ f)
    (hinf : f ∞ = ∞) : f ∈ Hpp :=
  ⟨Subgroup.subset_closure hf, hinf⟩

lemma G0_le_Hpp : G0 ≤ Hpp := by
  rw [G0, Subgroup.closure_le]
  rintro f (rfl | rfl | rfl)
  · exact mem_Hpp_of a_piecewise a_infty
  · exact mem_Hpp_of b_piecewise b_infty
  · exact mem_Hpp_of c_piecewise c_infty

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Filter Topology Set
open scoped ENNReal

/-! ### Statement 3: `φ` and `Φ` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore MeasureTheory Set
open scoped ENNReal

section Orbit

variable {X : Type*} [MeasurableSpace X] (Γ : Type) [Group Γ] [MulAction Γ X]

variable {Γ}

end Orbit

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2 MeasureTheory Set

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set Matrix

@[simp] lemma ent_kTrans_00 : ent kTrans 0 0 = 1 := rfl
@[simp] lemma ent_kTrans_01 : ent kTrans 0 1 = 1 := rfl
@[simp] lemma ent_kTrans_10 : ent kTrans 1 0 = 0 := rfl
@[simp] lemma ent_kTrans_11 : ent kTrans 1 1 = 1 := rfl
@[simp] lemma ent_kInv_00 : ent kInv 0 0 = 0 := rfl
@[simp] lemma ent_kInv_01 : ent kInv 0 1 = 1 := rfl
@[simp] lemma ent_kInv_10 : ent kInv 1 0 = -1 := rfl
@[simp] lemma ent_kInv_11 : ent kInv 1 1 = 0 := rfl
@[simp] lemma ent_kDil_00 : ent kDil 0 0 = Real.sqrt 2 := rfl
@[simp] lemma ent_kDil_01 : ent kDil 0 1 = 0 := rfl
@[simp] lemma ent_kDil_10 : ent kDil 1 0 = 0 := rfl
@[simp] lemma ent_kDil_11 : ent kDil 1 1 = 1 / Real.sqrt 2 := rfl

/-! ### Möbius maps are continuous and preserve null sets (from the Monod development) -/

section Mob

variable {A : Subring ℝ}

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

theorem polishSpace_P1 : PolishSpace (OnePoint ℝ) := by
  have e := onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)
  have : PolishSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_sphere.polishSpace
  exact e.isClosedEmbedding.polishSpace

theorem sigmaFinite_volP1 : MeasureTheory.SigmaFinite volP1 :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.sigmaFinite_map

end Mob

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set Matrix

/-! ### Statement 10: `G₀`- and `K`-orbits of irrational points -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set MeasureTheory

/-! ### The Carrière–Ghys ping-pong argument for a countable subgroup `Λ` of `SL(2, ℝ)`

Monod's development (`Monod.Dev.CG.A8`) runs the argument for the orbit relation of `SL(2, A)`;
here it is run for the orbit relation of any countable subgroup `Λ` containing `a_t`, `b_t` and
a ping-pong set `S ⊆ Λ`. -/

section CGL

attribute [local instance] secondCountable_P1

variable {Λ}

end CGL


/-! ### The Carrière–Ghys argument for `K` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod MeasureTheory

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.S2
theorem solution :
    G0 ≤ Monod.Hpp ∧ Chou.NoFreeSubgroupOfRankTwo G0 := by
  refine ⟨G0_le_Hpp, fun f hf => ?_⟩
  exact Monod.noFreeSubgroupOfRankTwo_Hpp.1 ((Subgroup.inclusion G0_le_Hpp).comp f)
    ((Subgroup.inclusion_injective G0_le_Hpp).comp hf)
end
