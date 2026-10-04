-- Prove2me | solution 1 for LodhaMoore.orbit_G0_eq_orbit_K_of_irrational
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.863965+00:00
-- url     : https://prove2.me/submissions/3287c177-3092-4997-8724-2c228ccb8b2b

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_LodhaMoore_eqOn_two_mul_and_eqOn_neg_inv

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

/-- `t ↦ t + 1`. -/
noncomputable def mTrans : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) :=
  mk2 1 1 0 1 (by norm_num)

lemma a_eq_mob (y : OnePoint ℝ) : a y = mob mTrans y := by
  cases y with
  | infty => rw [a_infty, mTrans, mob_mk2_infty _ _ _ _ _ rfl]
  | coe t =>
    rw [a_coe, mTrans, mob_mk2_coe _ _ _ _ _ _ (by norm_num)]
    congr 1; simp [aFun]

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

/-- The quotient map `SL(2, ℝ) → PSL(2, ℝ)`. -/
noncomputable abbrev pr : SLR →* PSLR := QuotientGroup.mk' _

lemma slr_ext {A B : SLR} (h : ∀ i j, ent A i j = ent B i j) : A = B := by
  ext i j
  exact h i j

lemma ent_mul (A B : SLR) (i j : Fin 2) :
    ent (A * B) i j = ent A i 0 * ent B 0 j + ent A i 1 * ent B 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

lemma ent_one (i j : Fin 2) : ent (1 : SLR) i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [ent]

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

/-- The upper unipotent `t ↦ t + x`. -/
noncomputable def uu (x : ℝ) : SLR := mk2 1 x 0 1 (by ring)
/-- The lower unipotent `t ↦ t / (x t + 1)`. -/
noncomputable def ll (x : ℝ) : SLR := mk2 1 0 x 1 (by ring)

lemma uu_add (x y : ℝ) : uu x * uu y = uu (x + y) := by
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ent_mul, uu]
  ring

lemma uu_zero : uu 0 = 1 := by
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ent_one, uu]

lemma uu_one : uu 1 = kTrans := by
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [uu]

lemma kInv_uu (y : ℝ) : kInv * uu y = ll (-y) * kInv := by
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ent_mul, uu, ll]

/-- The preimage of `K` in `SL(2, ℝ)`. -/
noncomputable def Kt : Subgroup SLR := K.comap pr

lemma kTrans_mem : kTrans ∈ Kt := Subgroup.subset_closure (by simp)
lemma kInv_mem : kInv ∈ Kt := Subgroup.subset_closure (by simp)
lemma kDil_mem : kDil ∈ Kt := Subgroup.subset_closure (by simp)

lemma uu_int_mem (n : ℤ) : uu n ∈ Kt := by
  have h : ∀ n : ℤ, uu n = kTrans ^ n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [uu_zero]
    | succ n ih =>
      rw [_root_.zpow_add_one, ← ih, ← uu_one, uu_add]
      push_cast; rfl
    | pred n ih =>
      have e : uu (-1) = kTrans⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← uu_one, uu_add]; norm_num [uu_zero]
      rw [_root_.zpow_sub_one, ← ih, ← e, uu_add]
      push_cast; ring_nf
  rw [h]
  exact Kt.zpow_mem kTrans_mem n

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

lemma a_mem : a ∈ G0 := Subgroup.subset_closure (by simp)
lemma b_mem : b ∈ G0 := Subgroup.subset_closure (by simp)
lemma c_mem : c ∈ G0 := Subgroup.subset_closure (by simp)

lemma ll_int_mem (n : ℤ) : ll n ∈ Kt := by
  have e : ll n = kInv * uu (-n : ℤ) * kInv⁻¹ := by
    rw [kInv_uu]; push_cast; rw [neg_neg, mul_assoc, mul_inv_cancel, mul_one]
  rw [e]
  exact Kt.mul_mem (Kt.mul_mem kInv_mem (uu_int_mem _)) (Kt.inv_mem kInv_mem)

lemma mob_uu_coe (x t : ℝ) : mob (uu x) (t : OnePoint ℝ) = ((t + x : ℝ) : OnePoint ℝ) := by
  rw [uu, mob_mk2_coe _ _ _ _ _ _ (by norm_num)]
  congr 1; ring

/-- Every element of `G₀` acts at each point as some element of `K`. -/
lemma G0_pointwise_K {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ G0) (x : OnePoint ℝ) :
    ∃ A : SLR, A ∈ Kt ∧ g x = mob A x := by
  induction hg using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    rcases hg with rfl | rfl | rfl
    · refine ⟨kTrans, kTrans_mem, ?_⟩
      rw [a_eq_mob, ← uu_one]; rfl
    · cases x with
      | infty => exact ⟨1, Kt.one_mem, by rw [b_infty, mob_one]⟩
      | coe t =>
        by_cases h0 : t ≤ 0
        · refine ⟨1, Kt.one_mem, ?_⟩
          rw [b_coe, mob_one]; simp [bFun, h0]
        by_cases h12 : t ≤ 1 / 2
        · refine ⟨ll (-1), by exact_mod_cast ll_int_mem (-1), ?_⟩
          rw [b_coe, ll, mob_mk2_coe _ _ _ _ _ _ (by linarith)]
          congr 1
          simp only [bFun, h0, h12, if_true, if_false]
          ring
        by_cases h1 : t ≤ 1
        · have e : mk2 3 (-1) 1 0 (by norm_num) = uu 3 * kInv⁻¹ := by
            rw [eq_mul_inv_iff_mul_eq]
            apply slr_ext; intro i j
            fin_cases i <;> fin_cases j <;> simp [ent_mul, uu]
          refine ⟨mk2 3 (-1) 1 0 (by norm_num), ?_, ?_⟩
          · rw [e]; exact Kt.mul_mem (by exact_mod_cast uu_int_mem 3) (Kt.inv_mem kInv_mem)
          · have ht : (0 : ℝ) < t := by linarith
            rw [b_coe, mob_mk2_coe _ _ _ _ _ _ (by linarith)]
            congr 1
            simp only [bFun, h0, h12, h1, if_true, if_false]
            field_simp
            ring
        · refine ⟨kTrans, kTrans_mem, ?_⟩
          rw [b_coe, ← uu_one, mob_uu_coe]
          congr 1
          simp only [bFun, h0, h12, h1, if_false]
    · cases x with
      | infty => exact ⟨1, Kt.one_mem, by rw [c_infty, mob_one]⟩
      | coe t =>
        by_cases h : 0 ≤ t ∧ t ≤ 1
        · have hs2 : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by field_simp
          have e : mk2 (Real.sqrt 2) 0 (1 / Real.sqrt 2) (1 / Real.sqrt 2) (by rw [hs2]; ring) =
              kDil * ll 1 := by
            apply slr_ext; intro i j
            fin_cases i <;> fin_cases j <;> simp [ent_mul, ll]
          refine ⟨mk2 (Real.sqrt 2) 0 (1 / Real.sqrt 2) (1 / Real.sqrt 2) (by rw [hs2]; ring),
            ?_, ?_⟩
          · rw [e]; exact Kt.mul_mem kDil_mem (by exact_mod_cast ll_int_mem 1)
          · have hpos : 0 < 1 / Real.sqrt 2 * t + 1 / Real.sqrt 2 := by
              have := h.1; positivity
            rw [c_coe, mob_mk2_coe _ _ _ _ _ _ hpos.ne']
            congr 1
            rw [cFun, if_pos h]
            have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
            rw [div_eq_div_iff (by linarith [h.1]) hpos.ne']
            field_simp
            linear_combination (-(t + t ^ 2)) * h22
        · refine ⟨1, Kt.one_mem, ?_⟩
          rw [c_coe, mob_one]; simp [cFun, h]
  | one => exact ⟨1, Kt.one_mem, by rw [mob_one]; rfl⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨A, hA, eA⟩ := ihh x
    obtain ⟨B, hB, eB⟩ := ihg (h x)
    refine ⟨B * A, Kt.mul_mem hB hA, ?_⟩
    rw [Homeomorph.mul_apply, eB, eA, mob_mul]
  | inv g _ ihg =>
    obtain ⟨A, hA, eA⟩ := ihg (g⁻¹ x)
    refine ⟨A⁻¹, Kt.inv_mem hA, ?_⟩
    have : g (g⁻¹ x) = x := by simp [Homeomorph.inv_apply]
    rw [this] at eA
    calc g⁻¹ x = mob A⁻¹ (mob A (g⁻¹ x)) := (mob_inv_mob _ _).symm
      _ = mob A⁻¹ x := by rw [← eA]

/-- `u` and `v` are in the same `G₀`-orbit. -/
def GOrb (u v : OnePoint ℝ) : Prop := ∃ g ∈ G0, g u = v

lemma GOrb_refl (u : OnePoint ℝ) : GOrb u u := ⟨1, G0.one_mem, rfl⟩

lemma GOrb_symm {u v : OnePoint ℝ} (h : GOrb u v) : GOrb v u := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, G0.inv_mem hg, by simp [Homeomorph.inv_apply]⟩

lemma GOrb_trans {u v w : OnePoint ℝ} (h1 : GOrb u v) (h2 : GOrb v w) : GOrb u w := by
  obtain ⟨g, hg, rfl⟩ := h1
  obtain ⟨h, hh, rfl⟩ := h2
  exact ⟨h * g, G0.mul_mem hh hg, rfl⟩

lemma a_pow_coe (k : ℕ) (y : ℝ) : (a ^ k) (y : OnePoint ℝ) = ((y + k : ℝ) : OnePoint ℝ) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Homeomorph.mul_apply, a_coe, ih]
    congr 1; simp [aFun]; ring

/- Proved through `ℕ` rather than by `induction k using Int.induction_on generalizing y`: that
proof makes the LeanInfo statement check (`same_statement_as`) fail for the whole file. -/
lemma a_zpow_coe (k : ℤ) (y : ℝ) : (a ^ k) (y : OnePoint ℝ) = ((y + k : ℝ) : OnePoint ℝ) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast, a_pow_coe]; simp
  · rw [_root_.zpow_neg, zpow_natCast, Homeomorph.inv_apply, Homeomorph.symm_apply_eq, a_pow_coe]
    congr 1; push_cast; ring

lemma op_mem {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ G0) : MulOpposite.op g ∈ G0.op := hg

/-- Doubling: `y` and `2y` are in the same `G₀`-orbit. -/
lemma GOrb_two_mul (y : ℝ) : GOrb (y : OnePoint ℝ) ((2 * y : ℝ) : OnePoint ℝ) := by
  set D := MulOpposite.op b * MulOpposite.op c * (MulOpposite.op a)⁻¹ * (MulOpposite.op c)⁻¹ *
    MulOpposite.op a
  have hD : D ∈ G0.op := by
    have ha := op_mem a_mem
    have hb := op_mem b_mem
    have hc := op_mem c_mem
    exact G0.op.mul_mem (G0.op.mul_mem (G0.op.mul_mem (G0.op.mul_mem hb hc) (G0.op.inv_mem ha))
      (G0.op.inv_mem hc)) ha
  set n := ⌊y⌋
  have hs : y - n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [Int.floor_le y], by linarith [Int.lt_floor_add_one y]⟩
  have hDs := eqOn_two_mul_and_eqOn_neg_inv.1 (y - n) hs
  refine ⟨a ^ (2 * n) * MulOpposite.unop D * a ^ (-n), G0.mul_mem (G0.mul_mem
    (G0.zpow_mem a_mem _) hD) (G0.zpow_mem a_mem _), ?_⟩
  rw [Homeomorph.mul_apply, Homeomorph.mul_apply, a_zpow_coe]
  have e1 : y + ((-n : ℤ) : ℝ) = y - n := by push_cast; ring
  rw [e1, hDs, a_zpow_coe]
  congr 1; push_cast; ring

lemma GOrb_two_pow_mul (k : ℕ) (y : ℝ) : GOrb (y : OnePoint ℝ) ((2 ^ k * y : ℝ) : OnePoint ℝ) := by
  induction k generalizing y with
  | zero => simpa using GOrb_refl _
  | succ k ih =>
    refine GOrb_trans (ih y) ?_
    have := GOrb_two_mul (2 ^ k * y)
    rwa [← mul_assoc, ← pow_succ'] at this

lemma GOrb_zpow_mul (m : ℤ) (y : ℝ) : GOrb (y : OnePoint ℝ) (((2 : ℝ) ^ m * y : ℝ) : OnePoint ℝ) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using GOrb_two_pow_mul k y
  · apply GOrb_symm
    rw [_root_.zpow_neg, zpow_natCast]
    have := GOrb_two_pow_mul k (((2 : ℝ) ^ k)⁻¹ * y)
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this

/-- Inversion: for `x ≠ 0`, `x` and `-1/x` are in the same `G₀`-orbit. -/
lemma GOrb_neg_inv {x : ℝ} (hx : x ≠ 0) : GOrb (x : OnePoint ℝ) ((-1 / x : ℝ) : OnePoint ℝ) := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow (abs_pos.2 hx) (one_lt_two : (1 : ℝ) < 2)
  set z := (2 : ℝ) ^ (-(n + 1)) * x
  have hp : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hz : (2 : ℝ) ^ (-(n + 1)) = 1 / 2 ^ (n + 1) := by rw [_root_.zpow_neg, one_div]
  have habs : |z| ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    have e : |z| = |x| / 2 ^ (n + 1) := by
      rw [abs_mul, abs_of_pos (by positivity), hz]; ring
    rw [e, zpow_add_one₀ (two_ne_zero)] at *
    have hp' : (0 : ℝ) < 2 ^ n := by positivity
    constructor
    · rw [le_div_iff₀ (by positivity)]; linarith
    · rw [div_le_iff₀ (by positivity)]; linarith
  have hJ : GOrb (z : OnePoint ℝ) ((-1 / z : ℝ) : OnePoint ℝ) := by
    rcases le_or_gt 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0] at habs
      have ha := op_mem a_mem
      have hb := op_mem b_mem
      refine ⟨MulOpposite.unop (MulOpposite.op b * (MulOpposite.op a)⁻¹ ^ (3 : ℕ)), ?_,
        eqOn_two_mul_and_eqOn_neg_inv.2.2 z habs⟩
      exact G0.op.mul_mem hb (G0.op.pow_mem (G0.op.inv_mem ha) 3)
    · rw [abs_of_neg hz0] at habs
      have ha := op_mem a_mem
      have hb := op_mem b_mem
      refine ⟨MulOpposite.unop (MulOpposite.op a * MulOpposite.op b * MulOpposite.op a), ?_,
        eqOn_two_mul_and_eqOn_neg_inv.2.1 z ⟨by linarith [habs.2], by linarith [habs.1]⟩⟩
      exact G0.op.mul_mem (G0.op.mul_mem ha hb) ha
  have h1 : GOrb (x : OnePoint ℝ) (z : OnePoint ℝ) := GOrb_zpow_mul _ x
  have h2 : GOrb ((-1 / z : ℝ) : OnePoint ℝ) ((-1 / x : ℝ) : OnePoint ℝ) := by
    have := GOrb_zpow_mul (-(n + 1)) (-1 / z)
    convert this using 2
    rw [hz]
    have hx2 : (2 : ℝ) ^ (n + 1) ≠ 0 := hp.ne'
    simp only [z, hz]
    field_simp
  exact GOrb_trans h1 (GOrb_trans hJ h2)

/-- `B` maps every irrational `x` to an irrational `y` in the `G₀`-orbit of `x`. -/
def QK (B : SLR) : Prop :=
  ∀ x : ℝ, Irrational x → ∃ y : ℝ, Irrational y ∧ mob B (x : OnePoint ℝ) = (y : OnePoint ℝ) ∧
    GOrb (x : OnePoint ℝ) (y : OnePoint ℝ)

lemma QK_congr {A B : SLR} (h : (QuotientGroup.mk A : PSLR) = QuotientGroup.mk B) (hB : QK B) :
    QK A := by
  intro x hx
  obtain ⟨y, hy, e, hr⟩ := hB x hx
  exact ⟨y, hy, by rw [mob_eq_of_pr_eq h, e], hr⟩

lemma mob_kDil_coe (x : ℝ) : mob kDil (x : OnePoint ℝ) = ((2 * x : ℝ) : OnePoint ℝ) := by
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [mob_coe, if_neg (by simp [h0])]
  congr 1
  simp only [ent_kDil_00, ent_kDil_01, ent_kDil_10, ent_kDil_11, zero_mul, zero_add, add_zero]
  field_simp
  linear_combination x * h22

lemma mob_kInv_coe {x : ℝ} (hx : x ≠ 0) : mob kInv (x : OnePoint ℝ) = ((-1 / x : ℝ) : OnePoint ℝ) := by
  rw [mob_coe, if_neg (by simp [hx])]
  congr 1
  simp only [ent_kInv_00, ent_kInv_01, ent_kInv_10, ent_kInv_11]
  rw [zero_mul, zero_add, add_zero, neg_one_mul, div_neg, neg_div]

lemma QK_kTrans : QK kTrans := fun x hx =>
  ⟨x + 1, by simpa using hx.add_natCast 1, by rw [← uu_one, mob_uu_coe],
    ⟨a, a_mem, by rw [a_coe]; rfl⟩⟩

lemma QK_kTrans_inv : QK kTrans⁻¹ := fun x hx => by
  have e : kTrans⁻¹ = uu (-1) := by
    rw [inv_eq_iff_mul_eq_one, ← uu_one, uu_add]; norm_num [uu_zero]
  refine ⟨x - 1, by simpa using hx.sub_natCast 1, by rw [e, mob_uu_coe]; congr 1, ?_⟩
  apply GOrb_symm
  exact ⟨a, a_mem, by rw [a_coe]; congr 1; simp [aFun]⟩

lemma QK_kInv : QK kInv := fun x hx => by
  have hx0 : x ≠ 0 := hx.ne_zero
  refine ⟨-1 / x, by rw [neg_div, one_div]; exact hx.inv.neg, mob_kInv_coe hx0,
    GOrb_neg_inv hx0⟩

lemma QK_kInv_inv : QK kInv⁻¹ := fun x hx => by
  have hx0 : x ≠ 0 := hx.ne_zero
  have h1 : (-1 / x : ℝ) ≠ 0 := by simp [hx0]
  have e : mob kInv ((-1 / x : ℝ) : OnePoint ℝ) = (x : OnePoint ℝ) := by
    rw [mob_kInv_coe h1]; congr 1; field_simp
  refine ⟨-1 / x, by rw [neg_div, one_div]; exact hx.inv.neg, ?_, GOrb_neg_inv hx0⟩
  rw [← e, mob_inv_mob]

lemma QK_kDil : QK kDil := fun x hx =>
  ⟨2 * x, by simpa using hx.natCast_mul (m := 2) two_ne_zero, mob_kDil_coe x, GOrb_two_mul x⟩

lemma QK_kDil_inv : QK kDil⁻¹ := fun x hx => by
  have e : mob kDil ((x / 2 : ℝ) : OnePoint ℝ) = (x : OnePoint ℝ) := by
    rw [mob_kDil_coe]; congr 1; ring
  refine ⟨x / 2, by simpa using hx.div_natCast (m := 2) two_ne_zero, by rw [← e, mob_inv_mob], ?_⟩
  apply GOrb_symm
  have := GOrb_two_mul (x / 2)
  rwa [show 2 * (x / 2) = x by ring] at this

lemma QK_of_mem_K {A : SLR} (hA : (QuotientGroup.mk A : PSLR) ∈ K) : QK A := by
  suffices h : ∀ p ∈ K, ∀ A : SLR, (QuotientGroup.mk A : PSLR) = p → QK A from h _ hA A rfl
  intro p hp
  induction hp using Subgroup.closure_induction'' with
  | mem p hp =>
    intro A hA
    rcases hp with rfl | rfl | rfl
    · exact QK_congr hA QK_kTrans
    · exact QK_congr hA QK_kInv
    · exact QK_congr hA QK_kDil
  | inv_mem p hp =>
    intro A hA
    rcases hp with rfl | rfl | rfl
    · exact QK_congr (hA.trans (QuotientGroup.mk_inv _ _).symm) QK_kTrans_inv
    · exact QK_congr (hA.trans (QuotientGroup.mk_inv _ _).symm) QK_kInv_inv
    · exact QK_congr (hA.trans (QuotientGroup.mk_inv _ _).symm) QK_kDil_inv
  | one =>
    intro A hA
    refine QK_congr (hA.trans (QuotientGroup.mk_one _).symm) fun x hx => ⟨x, hx, mob_one _, GOrb_refl _⟩
  | mul p q _ _ ihp ihq =>
    intro A hA
    set A1 := Quotient.out p
    set A2 := Quotient.out q
    have h1 : (QuotientGroup.mk A1 : PSLR) = p := QuotientGroup.out_eq' p
    have h2 : (QuotientGroup.mk A2 : PSLR) = q := QuotientGroup.out_eq' q
    have h12 : (QuotientGroup.mk A : PSLR) = QuotientGroup.mk (A1 * A2) := by
      rw [hA, QuotientGroup.mk_mul, h1, h2]
    refine QK_congr h12 fun x hx => ?_
    obtain ⟨y, hy, ey, ry⟩ := ihq A2 h2 x hx
    obtain ⟨z, hz, ez, rz⟩ := ihp A1 h1 y hy
    exact ⟨z, hz, by rw [mob_mul, ey, ez], GOrb_trans ry rz⟩

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
open LodhaMoore
open LodhaMoore.Dev.S2
theorem solution (t : ℝ) (ht : Irrational t) :
    {y : OnePoint ℝ | ∃ g ∈ G0, g (t : OnePoint ℝ) = y} =
      {y : OnePoint ℝ | ∃ A : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
        (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) ∈ K ∧
          Monod.mob A (t : OnePoint ℝ) = y} := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨A, hA, e⟩ := G0_pointwise_K hg (t : OnePoint ℝ)
    exact ⟨A, hA, e.symm⟩
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨z, _, ez, g, hg, hgz⟩ := QK_of_mem_K hA t ht
    exact ⟨g, hg, by rw [hgz, ez]⟩
end
