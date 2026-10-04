-- Prove2me | solution 1 for LodhaMoore.not_isMuAmenable_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T07:28:17.848769+00:00
-- url     : https://prove2.me/submissions/be61babd-495e-4c99-a23d-1decac120ecc

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_Chou_Classes
import Definitions.Def_Garrido_Amenability
import Theorems.Thm_LodhaMoore_isAmenableRel_of_isMuAmenable
import Theorems.Thm_CarriereGhys_not_isAmenableRel_orbit_of_dense

section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

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

lemma det_ent {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun x : A => (x : ℝ)) h
  simpa using this

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

lemma mob_mul {A : Subring ℝ} (g h : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (g * h) x = mob g (mob h x) := by
  unfold mob
  rw [map_mul, mul_smul]

lemma mob_one {A : Subring ℝ} (x : OnePoint ℝ) :
    mob (1 : Matrix.SpecialLinearGroup (Fin 2) A) x = x := by
  unfold mob
  rw [map_one, one_smul]

lemma mob_inv_mob {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g⁻¹ (mob g x) = x := by
  rw [← mob_mul, inv_mul_cancel, mob_one]

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

/-! ### Statement 1: `G₀ ≤ H` -/

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

abbrev SLR := SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)
abbrev PSLR := ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)

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

lemma ent_of_mem_center {z : SLR} (hz : z ∈ Subgroup.center SLR) :
    ∃ r : ℝ, r ^ 2 = 1 ∧ ent z 0 0 = r ∧ ent z 1 1 = r ∧ ent z 0 1 = 0 ∧ ent z 1 0 = 0 := by
  obtain ⟨r, hr1, hr2⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have e : ∀ i j, (z : Matrix (Fin 2) (Fin 2) (⊤ : Subring ℝ)) i j =
      (Matrix.scalar (Fin 2) r) i j := fun i j => by rw [hr2]
  refine ⟨(r : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hr1
    simpa using this
  · simp [ent, e 0 0]
  · simp [ent, e 1 1]
  · simp [ent, e 0 1]
  · simp [ent, e 1 0]

lemma mob_of_mem_center {z : SLR} (hz : z ∈ Subgroup.center SLR) (x : OnePoint ℝ) :
    mob z x = x := by
  obtain ⟨r, hr, h00, h11, h01, h10⟩ := ent_of_mem_center hz
  have hr0 : r ≠ 0 := by rintro rfl; norm_num at hr
  cases x with
  | infty => rw [mob_infty, if_pos h10]
  | coe t =>
    rw [mob_coe, h00, h11, h01, h10, if_neg (by simpa using hr0)]
    congr 1
    rw [add_zero, zero_mul, zero_add, mul_comm, mul_div_assoc, div_self hr0, mul_one]

lemma mob_eq_of_pr_eq {A B : SLR} (h : (QuotientGroup.mk A : PSLR) = QuotientGroup.mk B)
    (x : OnePoint ℝ) : mob A x = mob B x := by
  have hz : A⁻¹ * B ∈ Subgroup.center SLR := QuotientGroup.eq.1 h
  have : B = A * (A⁻¹ * B) := by group
  rw [this, mob_mul, mob_of_mem_center hz]

/-! ### Möbius maps are continuous and preserve null sets (from the Monod development) -/

section Mob

variable {A : Subring ℝ}

lemma tendsto_coe_cobounded :
    Tendsto (fun x : ℝ => (x : OnePoint ℝ)) (Bornology.cobounded ℝ) (𝓝 ∞) := by
  rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact]
  exact tendsto_coe_infty

lemma tendsto_affine_cobounded {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    Tendsto (fun x : ℝ => c * x + d) (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 := tendsto_norm_cobounded_atTop (E := ℝ)
  have h2 : Tendsto (fun x : ℝ => |c| * ‖x‖ - |d|) (Bornology.cobounded ℝ) atTop := by
    apply tendsto_atTop_add_const_right
    exact h1.const_mul_atTop (abs_pos.2 hc)
  refine tendsto_atTop_mono (fun x => ?_) h2
  simp only [Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (c * x) (-d)
  rw [abs_mul, abs_neg, sub_neg_eq_add] at this
  linarith

lemma frac_eq (g : Matrix.SpecialLinearGroup (Fin 2) A) {x : ℝ} (hc : ent g 1 0 ≠ 0)
    (hx : ent g 1 0 * x + ent g 1 1 ≠ 0) :
    (ent g 0 0 * x + ent g 0 1) / (ent g 1 0 * x + ent g 1 1) =
      ent g 0 0 / ent g 1 0 - (ent g 1 0 * (ent g 1 0 * x + ent g 1 1))⁻¹ := by
  have := det_ent g
  rw [eq_sub_iff_add_eq, div_eq_mul_inv, mul_inv, ← add_mul, ← div_eq_mul_inv]
  rw [div_eq_div_iff hx hc, add_mul, inv_mul_cancel₀ hc]
  linear_combination (-1 : ℝ) * this

lemma continuous_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) : Continuous (mob g) := by
  have hdet := det_ent g
  rw [OnePoint.continuous_iff]
  constructor
  · rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    by_cases hc : ent g 1 0 = 0
    · have hd : ent g 1 1 ≠ 0 := by
        intro h; rw [h, hc] at hdet; simp at hdet
      rw [mob_infty, if_pos hc]
      have : (fun x : ℝ => mob g (x : OnePoint ℝ)) =
          fun x : ℝ => (((ent g 0 0 / ent g 1 1) * x + ent g 0 1 / ent g 1 1 : ℝ) : OnePoint ℝ) := by
        funext x
        rw [mob_coe, if_neg (by rw [hc]; simpa using hd)]
        congr 1
        rw [hc, zero_mul, zero_add]; field_simp
      rw [this]
      have ha : ent g 0 0 ≠ 0 := by
        intro h; rw [h, hc] at hdet; simp at hdet
      exact tendsto_coe_cobounded.comp (tendsto_affine_cobounded (div_ne_zero ha hd) _)
    · rw [mob_infty, if_neg hc]
      have hev : ∀ᶠ x : ℝ in Bornology.cobounded ℝ, ent g 1 0 * x + ent g 1 1 ≠ 0 := by
        have := (tendsto_affine_cobounded hc (ent g 1 1)).eventually
          (Bornology.eventually_ne_cobounded (0 : ℝ))
        exact this
      have hlim : Tendsto (fun x : ℝ => ((ent g 0 0 / ent g 1 0 -
          (ent g 1 0 * (ent g 1 0 * x + ent g 1 1))⁻¹ : ℝ) : OnePoint ℝ))
          (Bornology.cobounded ℝ) (𝓝 ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ)) := by
        apply (continuous_coe.tendsto _).comp
        have h3 : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1))
            (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
          have := tendsto_affine_cobounded (mul_ne_zero hc hc) (ent g 1 0 * ent g 1 1)
          refine this.congr (fun x => ?_)
          ring
        have h4 := (tendsto_inv₀_cobounded.comp h3)
        have := (tendsto_const_nhds (x := ent g 0 0 / ent g 1 0)).sub h4
        simpa using this
      refine hlim.congr' ?_
      filter_upwards [hev] with x hx
      rw [mob_coe, if_neg hx, frac_eq g hc hx]
  · rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : ent g 1 0 * t + ent g 1 1 = 0
    · have hc : ent g 1 0 ≠ 0 := by
        intro h; rw [h, zero_mul, zero_add] at ht; rw [ht, h] at hdet; simp at hdet
      show Tendsto (fun x : ℝ => mob g (x : OnePoint ℝ)) (𝓝 t) (𝓝 (mob g (t : OnePoint ℝ)))
      rw [mob_coe, if_pos ht, ← nhdsNE_sup_pure t, tendsto_sup]
      constructor
      · have h3 : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1))
            (𝓝[≠] t) (𝓝[≠] 0) := by
          apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          · have : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1)) (𝓝 t)
                (𝓝 (ent g 1 0 * (ent g 1 0 * t + ent g 1 1))) :=
              ((continuous_const.mul ((continuous_const.mul continuous_id).add
                continuous_const)).tendsto t)
            rw [ht, mul_zero] at this
            exact tendsto_nhdsWithin_of_tendsto_nhds this
          · filter_upwards [self_mem_nhdsWithin] with x hx
            simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
            intro h0
            rcases mul_eq_zero.1 h0 with h | h
            · exact hc h
            · apply hx
              have : ent g 1 0 * (x - t) = 0 := by linarith
              rcases mul_eq_zero.1 this with h' | h'
              · exact absurd h' hc
              · linarith
        have h4 := tendsto_inv₀_nhdsNE_zero.comp h3
        have h5 := (tendsto_const_add_cobounded (ent g 0 0 / ent g 1 0)).comp
          ((tendsto_neg_cobounded).comp h4)
        refine (tendsto_coe_cobounded.comp h5).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_compl_iff, mem_singleton_iff] at hx
        have hx' : ent g 1 0 * x + ent g 1 1 ≠ 0 := by
          intro h0; apply hx
          have : ent g 1 0 * (x - t) = 0 := by linarith
          rcases mul_eq_zero.1 this with h' | h'
          · exact absurd h' hc
          · linarith
        simp only [Function.comp_apply]
        rw [mob_coe, if_neg hx', frac_eq g hc hx', sub_eq_add_neg]
      · rw [tendsto_pure_left]
        intro s hs
        rw [mob_coe, if_pos ht]
        exact mem_of_mem_nhds hs
    · have hev : ∀ᶠ x : ℝ in 𝓝 t, ent g 1 0 * x + ent g 1 1 ≠ 0 :=
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt.eventually_ne ht
      have hcont : ContinuousAt (fun x : ℝ => (((ent g 0 0 * x + ent g 0 1) /
          (ent g 1 0 * x + ent g 1 1) : ℝ) : OnePoint ℝ)) t := by
        apply continuous_coe.continuousAt.comp
        exact (((continuous_const.mul continuous_id).add continuous_const).continuousAt).div
          (((continuous_const.mul continuous_id).add continuous_const).continuousAt) ht
      refine hcont.congr (Filter.EventuallyEq.symm ?_)
      filter_upwards [hev] with x hx
      rw [mob_coe, if_neg hx]

lemma measurable_mob {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    Measurable (mob g) :=
  (continuous_mob g).measurable

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

theorem polishSpace_P1 : PolishSpace (OnePoint ℝ) := by
  have e := onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)
  have : PolishSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_sphere.polishSpace
  exact e.isClosedEmbedding.polishSpace

theorem sigmaFinite_volP1 : MeasureTheory.SigmaFinite volP1 :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.sigmaFinite_map

lemma volP1_apply (Z : Set (OnePoint ℝ)) : volP1 Z = MeasureTheory.volume (((↑) : ℝ → OnePoint ℝ) ⁻¹' Z) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.map_apply MeasureTheory.volume Z

open MeasureTheory in
/-- Möbius maps send null sets to null sets (copied from `RedNull`). -/
lemma null_image_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) {S : Set (OnePoint ℝ)}
    (hS : volP1 S = 0) : volP1 (mob g '' S) = 0 := by
  rw [volP1_apply] at hS ⊢
  set a : ℝ := ((g 0 0 : A) : ℝ)
  set b : ℝ := ((g 0 1 : A) : ℝ)
  set c : ℝ := ((g 1 0 : A) : ℝ)
  set d : ℝ := ((g 1 1 : A) : ℝ)
  let φ : ℝ → ℝ := fun x => (a * x + b) / (c * x + d)
  let U : Set ℝ := {x | c * x + d ≠ 0}
  have hφ : DifferentiableOn ℝ φ (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact hx.2
  have h1 : volume (φ '' (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hφ
      (measure_mono_null Set.inter_subset_left hS)
  have hsub : ((↑) : ℝ → OnePoint ℝ) ⁻¹' (mob g '' S) ⊆
      φ '' (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U) ∪ ((↑) : ℝ → OnePoint ℝ) ⁻¹' {mob g ∞} := by
    rintro y ⟨z, hz, hzy⟩
    cases z with
    | infty => exact Or.inr (by simp [← hzy])
    | coe x =>
      left
      rw [mob, OnePoint.smul_some_eq_ite] at hzy
      split_ifs at hzy with hx
      · exact absurd hzy.symm (OnePoint.coe_ne_infty y)
      · exact ⟨x, ⟨hz, hx⟩, OnePoint.coe_injective hzy⟩
  refine measure_mono_null hsub (measure_union_null h1 ?_)
  exact (Set.countable_singleton _).preimage OnePoint.coe_injective |>.measure_zero _

end Mob

/-- The orbit relation on `P¹` of a subgroup `Γ` of `PSL(2, ℝ)`. -/
def orbRelP (Γ : Subgroup PSLR) : Set (OnePoint ℝ × OnePoint ℝ) :=
  {p | ∃ A : SLR, (QuotientGroup.mk A : PSLR) ∈ Γ ∧ mob A p.1 = p.2}

lemma orbRelP_eq (Γ : Subgroup PSLR) :
    orbRelP Γ = ⋃ γ : Γ, {p | mob (Quotient.out (γ : PSLR)) p.1 = p.2} := by
  ext p
  simp only [orbRelP, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨A, hA, hp⟩
    refine ⟨⟨_, hA⟩, ?_⟩
    rw [mob_eq_of_pr_eq (QuotientGroup.out_eq' _)]
    exact hp
  · rintro ⟨γ, hp⟩
    refine ⟨Quotient.out (γ : PSLR), ?_, hp⟩
    rw [QuotientGroup.out_eq']
    exact γ.2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

lemma measurableSet_orbRelP (Γ : Subgroup PSLR) [Countable Γ] : MeasurableSet (orbRelP Γ) := by
  rw [orbRelP_eq]
  exact MeasurableSet.iUnion fun γ =>
    measurableSet_eq_fun ((measurable_mob _).comp measurable_fst) measurable_snd

lemma equivalence_orbRelP (Γ : Subgroup PSLR) : Equivalence fun x y => (x, y) ∈ orbRelP Γ := by
  refine ⟨fun x => ⟨1, by simpa using Γ.one_mem, mob_one x⟩, ?_, ?_⟩
  · rintro x y ⟨A, hA, hp⟩
    refine ⟨A⁻¹, by simpa using Γ.inv_mem hA, ?_⟩
    simp only at hp ⊢
    rw [← hp, mob_inv_mob]
  · rintro x y z ⟨A, hA, hp⟩ ⟨B, hB, hq⟩
    refine ⟨B * A, by simpa using Γ.mul_mem hB hA, ?_⟩
    simp only at hp hq ⊢
    rw [mob_mul, hp, hq]

lemma countable_orbRelP (Γ : Subgroup PSLR) [Countable Γ] (x : OnePoint ℝ) :
    {y | (x, y) ∈ orbRelP Γ}.Countable := by
  refine (Set.countable_range fun γ : Γ => mob (Quotient.out (γ : PSLR)) x).mono ?_
  intro y hy
  rw [Set.mem_ofPred_eq, orbRelP_eq, Set.mem_iUnion] at hy
  obtain ⟨γ, hγ⟩ := hy
  exact ⟨γ, hγ⟩

lemma null_saturation_orbRelP (Γ : Subgroup PSLR) [Countable Γ] (Z : Set (OnePoint ℝ))
    (hZ : volP1 Z = 0) : volP1 {y | ∃ x ∈ Z, (x, y) ∈ orbRelP Γ} = 0 := by
  have : {y | ∃ x ∈ Z, (x, y) ∈ orbRelP Γ} ⊆ ⋃ γ : Γ, mob (Quotient.out (γ : PSLR)) '' Z := by
    rintro y ⟨x, hx, hxy⟩
    rw [orbRelP_eq, Set.mem_iUnion] at hxy
    obtain ⟨γ, hγ⟩ := hxy
    exact Set.mem_iUnion.2 ⟨γ, x, hx, hγ⟩
  exact MeasureTheory.measure_mono_null this
    (MeasureTheory.measure_iUnion_null fun γ => null_image_mob _ hZ)

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

variable (Λ : Subgroup SLR)

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
/-! # Lodha–Moore statement 7 from the published Carrière–Ghys theorem and statement 4 -/

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.S2
attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1
theorem solution
    (Γ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ))) [Countable Γ]
    (hΓ : Dense (Γ : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)))) :
    ¬ IsMuAmenable Monod.volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ A : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
        (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) ∈ Γ ∧
          Monod.mob A p.1 = p.2} := by
  intro h
  exact CarriereGhys.not_isAmenableRel_orbit_of_dense Γ hΓ
    (isAmenableRel_of_isMuAmenable Monod.volP1 (orbRelP Γ) (measurableSet_orbRelP Γ)
      (equivalence_orbRelP Γ) (countable_orbRelP Γ) (null_saturation_orbRelP Γ) h)
end
