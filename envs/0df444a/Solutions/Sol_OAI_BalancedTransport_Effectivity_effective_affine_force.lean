-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.effective_affine_force
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:30:01.950558+00:00
-- url     : https://prove2.me/submissions/c67075c2-abe8-4b1d-8b28-c6442498d96b

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RelativeForce.lean:L135-L217
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.effective_affine_force. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Theorems.Thm_OAI_BalancedTransport_Effectivity_nat_mul_error_shift

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.OracleComputability ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Encodable
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
variable {O : Set (ℕ →. ℕ)}

lemma computableIn_of_eq {f g : α → β} (hf : ComputableIn O f)
    (h : ∀ a, f a = g a) : ComputableIn O g := (funext h) ▸ hf

lemma computableIn_pair {f : α → β} {g : α → γ} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O (fun a => (f a, g a)) := by
  apply Nat.RecursiveIn.of_eq (Nat.RecursiveIn.pair hf hg)
  intro n
  cases decode (α := α) n <;> simp [Seq.seq]

lemma computableIn_comp {f : β → γ} {g : α → β} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O (fun a => f (g a)) := by
  apply Nat.RecursiveIn.of_eq (Nat.RecursiveIn.comp hf hg)
  intro n
  cases decode (α := α) n <;> simp

lemma computableIn_comp₂ {δ : Type*} [Primcodable δ] {f : β → γ → δ}
    {g : α → β} {h : α → γ} (hf : ComputableIn₂ O f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O (fun a => f (g a) (h a)) :=
  computableIn_comp hf (computableIn_pair hg hh)

lemma computableIn_fin_triple (f g h : α → β) (hf : ComputableIn O f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O (fun a => ![f a, g a, h a]) := by
  have hv : Primrec₂ (fun i : Fin 3 => fun p : β × β × β => (![p.1, p.2.1, p.2.2] : Fin 3 → β) i) := by
    apply Primrec.fin_curry₁.mpr
    intro i
    fin_cases i
    · exact Primrec.fst
    · exact Primrec.fst.comp Primrec.snd
    · exact Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : β × β × β => ![p.1, p.2.1, p.2.2]) :=
    Primrec.fin_curry.mpr (hv.comp Primrec.snd Primrec.fst)
  exact computableIn_comp hc.computableIn (computableIn_pair hf (computableIn_pair hg hh))

lemma computableIn_fin_eval {n : ℕ} {f : α → (Fin n → β)} (hf : ComputableIn O f)
    (i : Fin n) : ComputableIn O (fun a => f a i) :=
  computableIn_comp (Primrec.fin_app.comp Primrec.id (Primrec.const i)).computableIn hf

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RelativeForce ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity

lemma error_nonneg (n : ℕ) : 0 ≤ error n := by unfold error; positivity

lemma error_le_one (n : ℕ) : error n ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)

lemma computableIn_rat_add {α : Type*} [Primcodable α] {O : Set (ℕ →. ℕ)}
    {f g : α → ℚ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f a + g a) :=
  computableIn_comp (O := O) (f := fun p : ℚ × ℚ => p.1 + p.2) (g := fun a => (f a, g a))
    (Computable.computableIn computable_rat_add) (computableIn_pair hf hg)

lemma computableIn_rat_mul {α : Type*} [Primcodable α] {O : Set (ℕ →. ℕ)}
    {f g : α → ℚ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f a * g a) :=
  computableIn_comp (O := O) (f := fun p : ℚ × ℚ => p.1 * p.2) (g := fun a => (f a, g a))
    (Computable.computableIn computable_rat_mul) (computableIn_pair hf hg)

theorem effective_affine_force {O : Set (ℕ →. ℕ)} {v w : Velocity} {ν : ℝ}
    (hv : EffectiveFieldIn O v) (hw : EffectiveFieldIn O w)
    {name : ℕ → ℚ} (hc : ComputableIn O name) (hn : RealName name ν)
    (hlin : ∀ a t, 0 ≤ t → ∀ x,
      mixedD a (affineForce v w ν) t x = mixedD a v t x + ν • mixedD a w t x) :
    EffectiveFieldIn O (affineForce v w ν) := by
  obtain ⟨E₀, b₀, hE₀, hb₀, he₀, hbound₀⟩ := hv
  obtain ⟨E₁, b₁, hE₁, hb₁, he₁, hbound₁⟩ := hw
  obtain ⟨C, hC⟩ := exists_nat_ge |ν|
  let prec : MultiIndex × RationalPoint × ℕ → ℕ := fun s => s.2.2 + (C + b₁ s.1 + 2)
  have hb₁' : ComputableIn O (fun s : MultiIndex × RationalPoint × ℕ => b₁ s.1) :=
    computableIn_comp hb₁ ComputableIn.fst
  have hprec : ComputableIn O prec := by
    exact computableIn_comp₂ Primrec.nat_add.computableIn₂
      (computableIn_comp ComputableIn.snd ComputableIn.snd)
      (computableIn_comp₂ Primrec.nat_add.computableIn₂
        (computableIn_comp₂ Primrec.nat_add.computableIn₂ (ComputableIn.const C) hb₁')
        (ComputableIn.const 2))
  let arg : MultiIndex × RationalPoint × ℕ → MultiIndex × RationalPoint × ℕ :=
    fun s => (s.1, s.2.1, prec s)
  have harg : ComputableIn O arg := computableIn_pair ComputableIn.fst
    (computableIn_pair (computableIn_comp ComputableIn.fst ComputableIn.snd) hprec)
  let E : MultiIndex × RationalPoint × ℕ → Fin 3 → ℚ :=
    fun s i => E₀ (arg s) i + name (prec s) * E₁ (arg s) i
  have hi (i : Fin 3) : ComputableIn O (fun s => E s i) := by
    have h₀ : ComputableIn O (fun s => E₀ (arg s) i) :=
      computableIn_fin_eval (computableIn_comp hE₀ harg) i
    have h₁ : ComputableIn O (fun s => E₁ (arg s) i) :=
      computableIn_fin_eval (computableIn_comp hE₁ harg) i
    have hn' : ComputableIn O (fun s => name (prec s)) := computableIn_comp hc hprec
    exact computableIn_rat_add h₀ (computableIn_rat_mul hn' h₁)
  have hE : ComputableIn O E := by
    refine computableIn_of_eq (computableIn_fin_triple _ _ _ (hi 0) (hi 1) (hi 2)) ?_
    intro s
    ext i
    fin_cases i <;> rfl
  let b : MultiIndex → ℕ := fun a => b₀ a + C * b₁ a
  have hb : ComputableIn O b := computableIn_comp₂ Primrec.nat_add.computableIn₂ hb₀
    (computableIn_comp₂ Primrec.nat_mul.computableIn₂ (ComputableIn.const C) hb₁)
  refine ⟨E, b, hE, hb, ?_, ?_⟩
  · intro a z n hz i
    let k := prec (a,z,n)
    have h₀ := he₀ a z k hz i
    have h₁ := he₁ a z k hz i
    have hν := hn k
    have hνb : |(name k : ℝ)| ≤ C + 1 := by
      have htriangle : |(name k : ℝ)| ≤ |(name k : ℝ) - ν| + |ν| := by
        simpa only [sub_add_cancel] using abs_add_le ((name k : ℝ) - ν) ν
      linarith [error_le_one k]
    have hwval : |mixedD a w (z.1 : ℝ) (rationalSpace z.2) i| ≤ b₁ a :=
      (norm_le_pi_norm _ i).trans (hbound₁ a _ (by exact_mod_cast hz) _)
    have hid : (E (a,z,n) i : ℝ) -
        mixedD a (affineForce v w ν) (z.1 : ℝ) (rationalSpace z.2) i =
        ((E₀ (a,z,k) i : ℝ) - mixedD a v (z.1 : ℝ) (rationalSpace z.2) i) +
        (name k : ℝ) * ((E₁ (a,z,k) i : ℝ) - mixedD a w (z.1 : ℝ) (rationalSpace z.2) i) +
        ((name k : ℝ) - ν) * mixedD a w (z.1 : ℝ) (rationalSpace z.2) i := by
      rw [hlin a _ (by exact_mod_cast hz)]
      dsimp [E, arg, k]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ (error k + (C + 1) * error k) + error k * (b₁ a : ℝ) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (abs_add_le _ _).trans (add_le_add h₀ ?_)
          rw [abs_mul]
          exact mul_le_mul hνb h₁ (abs_nonneg _) (by positivity)
        · rw [abs_mul]
          exact mul_le_mul hν hwval (abs_nonneg _) (error_nonneg k)
      _ = (C + b₁ a + 2 : ℕ) * error (n + (C + b₁ a + 2)) := by
        dsimp [k, prec]
        push_cast
        ring
      _ ≤ error n := nat_mul_error_shift n _
  · intro a t ht x
    rw [hlin a t ht x]
    calc
      _ ≤ ‖mixedD a v t x‖ + ‖ν • mixedD a w t x‖ := norm_add_le _ _
      _ ≤ (b₀ a : ℝ) + C * (b₁ a : ℝ) := by
        apply add_le_add (hbound₀ a t ht x)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul hC (hbound₁ a t ht x) (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (b a : ℝ) := by simp [b]

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.effective_affine_force := @_root_.OAI.BalancedTransport.Effectivity.effective_affine_force
