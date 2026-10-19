-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.elementary_evacuateHighest
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:24:42.83065+00:00
-- url     : https://prove2.me/submissions/743b0b63-7472-431f-ba08-f0eb521de7e9

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryParking.lean:L10-L93
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.elementary_evacuateHighest. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Theorems.Thm_OAI_BalancedTransport_Effectivity_transition_denom_lower
import Theorems.Thm_OAI_BalancedTransport_Geometry_raising_gap

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FlatBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

lemma rhoJet_zero (x : ℝ) : rhoJet 0 x = expNegInvGlue x := by
  simp [rhoJet, rhoPolynomial]

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericScopes ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma real_append (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (s q : List ℝ) (hs : o.Scoped s.length) : o.real d x (s ++ q) = o.real d x s := by
  have he (i : ℕ) (hi : i < s.length) : (s ++ q).getD i 0 = s.getD i 0 := by
    simp [List.getD, List.getElem?_append_left hi]
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp only [Scoped, real, tag, rat, left, right] at hs ⊢
  all_goals first | rfl | exact he _ hs | simp only [he _ hs] | simp only [he _ hs.1, he _ hs.2]

lemma valid_append (o : NumericOp) (s q : List ℝ) (hs : o.Scoped s.length) :
    o.Valid (s ++ q) ↔ o.Valid s := by
  by_cases ht : o.tag = 5
  · have hh : o.left < s.length := by unfold Scoped at hs; rw [ht] at hs; exact hs
    simp only [Valid, ht, forall_const]
    simp only [List.getD, List.getElem?_append_left hh]
  · simp [Valid, ht]

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma realFrom_length (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (realFrom p x s).length = p.length + s.length := by
  induction p generalizing s with
  | nil => simp [realFrom]
  | cons o p ih => simpa [realFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (o.real d x s :: s)

lemma realFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : realFrom p x (s ++ q) = realFrom p x s ++ q := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change realFrom p x (o.real d x (s ++ q) :: (s ++ q)) =
      realFrom p x (o.real d x s :: s) ++ q
    rw [o.real_append d x s q hs.1]
    exact ih (o.real d x s :: s) hs.2

lemma validFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : ValidFrom x p (s ++ q) ↔ ValidFrom x p s := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change o.Valid (s ++ q) ∧ ValidFrom x p (o.real d x (s ++ q) :: (s ++ q)) ↔
      o.Valid s ∧ ValidFrom x p (o.real d x s :: s)
    rw [o.valid_append s q hs.1, o.real_append d x s q hs.1]
    exact and_congr_right (fun _ => ih (o.real d x s :: s) hs.2)

lemma realFrom_empty_append (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    realFrom p x s = realFrom p x [] ++ s :=
  realFrom_append p x [] s hp

lemma validFrom_of_closed (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    ValidFrom x p s ↔ p.Valid x := p.validFrom_append x [] s hp

lemma realFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).realFrom x s = q.realFrom x (realFrom p x s) := List.foldl_append

lemma validFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).ValidFrom x s ↔ ValidFrom x p s ∧ q.ValidFrom x (realFrom p x s) := by
  induction p generalizing s with
  | nil => simp [ValidFrom, realFrom]
  | cons o p ih => simpa only [List.cons_append, ValidFrom, realFrom,
      List.foldl_cons, and_assoc] using and_congr_right (fun _ => ih _)

lemma scopedFrom_mono (p : NumericProgram) {n m : ℕ} (hnm : n ≤ m) :
    p.ScopedFrom n → p.ScopedFrom m := by
  intro h
  induction p generalizing n m with
  | nil => trivial
  | cons o p ih =>
    refine ⟨?_, ih (Nat.add_le_add_right hnm 1) h.2⟩
    rcases o with ⟨j,r,a,b⟩
    have ho := h.1
    fin_cases j <;> dsimp only [NumericOp.Scoped, NumericOp.tag, NumericOp.rat,
      NumericOp.left, NumericOp.right] at ho ⊢
    all_goals first | trivial | exact ho.trans_le hnm | exact ⟨ho.1.trans_le hnm,ho.2.trans_le hnm⟩

lemma scopedFrom_concat (p q : NumericProgram) (n : ℕ) :
    (p ++ q).ScopedFrom n ↔ p.ScopedFrom n ∧ q.ScopedFrom (n+p.length) := by
  induction p generalizing n with
  | nil => simp [ScopedFrom]
  | cons o p ih =>
    simp only [List.cons_append, ScopedFrom, List.length_cons]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1, and_assoc]

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericAlgebra ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma literal_closed (q : ℚ) : (literal q).Closed := by trivial

lemma literal_valid (q : ℚ) (x : Fin d → ℝ) : (literal q).Valid x := by
  simp [literal, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

omit [NeZero d] in
lemma coordinate_closed (k : Fin d) : (coordinate k).Closed := by trivial

lemma coordinate_valid (k : Fin d) (x : Fin d → ℝ) : (coordinate k).Valid x := by
  simp [coordinate, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

lemma coordinate_real (k : Fin d) (x : Fin d → ℝ) : (coordinate k).real x = x k := by
  simp [coordinate, real, realFrom, NumericOp.real, NumericOp.tag, NumericOp.left, Fin.ofNat_eq_cast]

lemma unary_real (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ) :
    (unary j n p).real x = NumericOp.real d (j,0,0,n) x (p.realFrom x []) := by
  simp [unary, real, realFrom, List.foldl_append]

lemma unary_valid (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ)
    (hp : p.Valid x) (hi : j = 5 → ((n+1:ℕ):ℝ)⁻¹ ≤ p.real x) :
    (unary j n p).Valid x := by
  exact (validFrom_concat _ _ _ _).mpr ⟨hp, ⟨hi, trivial⟩⟩

lemma unary_closed (j : Fin 9) (n : ℕ) (p : NumericProgram) (hp : p.Closed)
    (hne : p ≠ []) (hj : j = 4 ∨ j = 5 ∨ j = 7) : (unary j n p).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hne
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨hp, ?_⟩
  rcases hj with rfl | rfl | rfl <;> exact ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.left] using hn,trivial⟩

lemma realFrom_head {s : List ℝ} (hs : 0 < s.length) (t : List ℝ) :
    (s ++ t).getD 0 0 = s.getD 0 0 := by
  simp only [List.getD, List.getElem?_append_left hs]

lemma binary_real (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ [])
    (x : Fin d → ℝ) :
    (binary j p q).real x =
      NumericOp.real d (j,0,q.length,0) x (q.realFrom x [] ++ p.realFrom x []) := by
  cases q with
  | nil => exact (hne rfl).elim
  | cons head tail =>
    simp only [binary, real, realFrom_concat]
    rw [realFrom_empty_append (head :: tail) hq]
    rfl

lemma binary_register_left (p q : NumericProgram) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD q.length 0 = p.real x := by
  have he := q.realFrom_length x []
  simp only [List.length_nil, Nat.add_zero] at he
  rw [← he]
  simp only [List.getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

lemma binary_register_right (p q : NumericProgram) (hne : q ≠ []) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD 0 0 = q.real x := by
  apply realFrom_head
  simpa only [realFrom_length, List.length_nil, Nat.add_zero] using List.length_pos_iff.mpr hne

lemma binary_valid (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hj : j ≠ 5)
    (x : Fin d → ℝ) (hpv : p.Valid x) (hqv : q.Valid x) : (binary j p q).Valid x := by
  apply (validFrom_concat _ _ _ _).mpr
  refine ⟨(validFrom_concat _ _ _ _).mpr ⟨hpv,
    (validFrom_of_closed q hq x _).mpr hqv⟩, ?_⟩
  exact ⟨fun h => (hj h).elim, trivial⟩

lemma binary_closed (j : Fin 9) (p q : NumericProgram) (hp : p.Closed) (hq : q.Closed)
    (hnep : p ≠ []) (hneq : q ≠ []) (hj : j = 2 ∨ j = 3) : (binary j p q).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hnep
  have hqn : 0 < q.length := List.length_pos_iff.mpr hneq
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨(scopedFrom_concat _ _ _).mpr ⟨hp, q.scopedFrom_mono (Nat.zero_le _) hq⟩, ?_⟩
  rcases hj with rfl | rfl <;>
    simp only [ScopedFrom, NumericOp.Scoped, NumericOp.tag, NumericOp.left,
      NumericOp.right, List.length_append]
  all_goals exact ⟨⟨by omega, by omega⟩,trivial⟩

lemma binary_add_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 2 p q).real x = p.real x + q.real x := by
  rw [binary_real 2 p q hq hne]
  exact congrArg₂ (· + ·) (binary_register_left p q x) (binary_register_right p q hne x)

lemma binary_mul_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 3 p q).real x = p.real x * q.real x := by
  rw [binary_real 3 p q hq hne]
  exact congrArg₂ (· * ·) (binary_register_left p q x) (binary_register_right p q hne x)

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e] {f g : (Fin d → ℝ) → ℝ}

lemma literal (q : ℚ) : Elementary (fun _ : Fin d → ℝ => (q : ℝ)) :=
  ⟨NumericProgram.literal q, by simp [NumericProgram.literal],
    NumericProgram.literal_closed q, NumericProgram.literal_valid q, rfl⟩

lemma coordinate (k : Fin d) : Elementary (fun z : Fin d → ℝ => z k) :=
  ⟨NumericProgram.coordinate k, by simp [NumericProgram.coordinate],
    NumericProgram.coordinate_closed k, NumericProgram.coordinate_valid k,
    funext (NumericProgram.coordinate_real k)⟩

lemma add (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x + g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 2 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 2 p q hpc hqc hpn hqn (Or.inl rfl),
    fun x => NumericProgram.binary_valid 2 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_add_real p q hqc hqn)⟩

lemma mul (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x * g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 3 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 3 p q hpc hqc hpn hqn (Or.inr rfl),
    fun x => NumericProgram.binary_valid 3 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_mul_real p q hqc hqn)⟩

lemma neg (hf : Elementary f) : Elementary (fun x => -f x) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 4 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 4 0 p hc hn (Or.inl rfl),
    fun x => NumericProgram.unary_valid 4 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma sub (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma inv (hf : Elementary f) (n : ℕ) (hn : ∀ x, ((n+1:ℕ):ℝ)⁻¹ ≤ f x) :
    Elementary (fun x => (f x)⁻¹) := by
  obtain ⟨p, hne, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 5 n p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 5 n p hc hne (Or.inr (Or.inl rfl)),
    fun x => NumericProgram.unary_valid 5 n p x (hv x) (fun _ => hn x), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma exp (hf : Elementary f) : Elementary (fun x => Real.exp (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 7 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 7 0 p hc hn (Or.inr (Or.inr rfl)),
    fun x => NumericProgram.unary_valid 7 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma rho (n : ℕ) (hf : Elementary f) : Elementary (fun x => rhoJet n (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p ++ [(6,0,n,0)], by simp, ?_, ?_, ?_⟩
  · apply (NumericProgram.scopedFrom_concat _ _ _).mpr
    exact ⟨hc, ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.right] using List.length_pos_iff.mpr hn, trivial⟩⟩
  · intro x
    exact (NumericProgram.validFrom_concat _ _ _ _).mpr ⟨hv x, ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩⟩
  · funext x
    simp only [NumericProgram.real, NumericProgram.realFrom_concat]
    rfl

lemma logLiteral (q : ℚ) : Elementary (fun _ : Fin d → ℝ => if 0 < q then Real.log (q : ℝ) else 0) := by
  refine ⟨[(8,q,0,0)], by simp, by simp [NumericProgram.Closed, NumericProgram.ScopedFrom, NumericOp.Scoped, NumericOp.tag], ?_, rfl⟩
  intro x
  exact ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e]

lemma zero : Elementary (fun _ : Fin d → ℝ => (0 : ℝ)) := by simpa using (literal (d := d) 0)

lemma one : Elementary (fun _ : Fin d → ℝ => (1 : ℝ)) := by simpa using (literal (d := d) 1)

lemma div_rat (q : ℚ) {f : (Fin d → ℝ) → ℝ} (hf : Elementary f) :
    Elementary (fun x => f x / (q : ℝ)) := by
  simpa [div_eq_mul_inv] using hf.mul (literal q⁻¹)

lemma operation (o : NumericOp) (g : (Fin d → ℝ) → (Fin e → ℝ))
    (s : (Fin d → ℝ) → List ℝ)
    (hg : ∀ k, Elementary (fun x => g x k))
    (hs : ∀ n, Elementary (fun x => (s x).getD n 0))
    (hv : ∀ x, o.Valid (s x)) : Elementary (fun x => o.real e (g x) (s x)) := by
  rcases o with ⟨j,q,a,b⟩
  fin_cases j <;> dsimp only [NumericOp.real, NumericOp.tag, NumericOp.rat,
    NumericOp.left, NumericOp.right]
  · exact literal q
  · exact hg _
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · exact (hs a).inv b (fun x => hv x rfl)
  · exact (hs b).rho a
  · exact (hs a).exp
  · exact logLiteral q

lemma program_registers (p : NumericProgram)
    (g : (Fin d → ℝ) → (Fin e → ℝ)) (s : (Fin d → ℝ) → List ℝ)
    (hg : ∀ k, Elementary (fun x => g x k))
    (hs : ∀ n, Elementary (fun x => (s x).getD n 0))
    (hv : ∀ x, p.ValidFrom (g x) (s x)) :
    ∀ n, Elementary (fun x => (p.realFrom (g x) (s x)).getD n 0) := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun x => o.real e (g x) (s x) :: s x)
    · intro n
      cases n with
      | zero => exact operation o g s hg hs (fun x => (hv x).1)
      | succ n => exact hs n
    · exact fun x => (hv x).2

lemma comp {f : (Fin e → ℝ) → ℝ} (hf : Elementary f)
    (g : (Fin d → ℝ) → (Fin e → ℝ))
    (hg : ∀ k, Elementary (fun x => g x k)) : Elementary (fun x => f (g x)) := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact program_registers p g (fun _ => []) hg (fun n => by simpa using (zero (d:=d)))
    (fun x => hv (g x)) 0

lemma smoothTransition {f : (Fin d → ℝ) → ℝ} (hf : Elementary f) :
    Elementary (fun x => Real.smoothTransition (f x)) := by
  have hρ : Elementary (fun x => expNegInvGlue (f x)) := by
    simpa only [rhoJet_zero] using hf.rho 0
  have hρ' : Elementary (fun x => expNegInvGlue (1 - f x)) := by
    simpa only [rhoJet_zero] using (one.sub hf).rho 0
  have hi := (hρ.add hρ').inv 8 (fun x => by
    simpa using transition_denom_lower (f x))
  simpa only [Real.smoothTransition, div_eq_mul_inv] using hρ.mul hi

end BalancedTransport.Effectivity.Elementary
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Parking ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma guarded_update {a w : ι → Space} {safe : Set ι}
    (ha : (BoxLayout.mk a w).Guarded safe) (i : ι) (b : Space)
    (hb : i ∈ safe → 2 < b 0 - w i 0) :
    (BoxLayout.mk (Function.update a i b) w).Guarded safe := by
  intro j hj
  by_cases hji : j = i
  · subst j; simpa using hb hj
  · simpa [Function.update_of_ne hji] using ha j hj

lemma high_plane_gap {p q z : Space} {H r D : ℝ} (hp : p 1 = H) (hq : q 1 = H)
    (hz : D < H - z 1) :
    ∃ k, D < |(1 - r) * p k + r * q k - z k| := by
  refine ⟨1, hz.trans_le ?_⟩
  rw [hp, hq]
  calc
    H - z 1 = (1 - r) * H + r * H - z 1 := by ring
    _ ≤ |(1 - r) * H + r * H - z 1| := le_abs_self _

lemma fixed_first_gap {p q z : Space} {r D : ℝ} (hpq : p 0 = q 0)
    (hz : D < |q 0 - z 0|) :
    ∃ k, D < |(1 - r) * p k + r * q k - z k| := by
  refine ⟨0, ?_⟩
  rw [hpq]
  convert hz using 1; congr 1; ring

omit [Fintype ι] in
lemma remainingCenters_separated {a p : ι → Space} {D : ℝ}
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|) (S : Finset ι) :
    CenterSeparated (remainingCenters a p S) D := by
  intro i j hij
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simpa [remainingCenters, hi, hj] using ha i j hij
  · exact ⟨0, by simpa [remainingCenters, hi, hj] using hcross i j⟩
  · exact ⟨0, by simpa [remainingCenters, hi, hj, abs_sub_comm] using hcross j i⟩
  · exact ⟨0, by simpa [remainingCenters, hi, hj] using hp i j hij⟩

omit [Fintype ι] in
lemma remainingCenters_guarded {a p w : ι → Space} {safe : Set ι}
    (ha : (BoxLayout.mk a w).Guarded safe) (hp : (BoxLayout.mk p w).Guarded safe)
    (S : Finset ι) : (BoxLayout.mk (remainingCenters a p S) w).Guarded safe := by
  intro i hi
  by_cases h : i ∈ S
  · simpa [remainingCenters, h] using ha i hi
  · simpa [remainingCenters, h] using hp i hi

omit [Fintype ι] in
lemma remainingCenters_erase {a p : ι → Space} {S : Finset ι} {i : ι} (_hi : i ∈ S) :
    remainingCenters a p (S.erase i) = Function.update (remainingCenters a p S) i (p i) := by
  ext j k
  by_cases hji : j = i
  · subst j; simp [remainingCenters]
  · simp [remainingCenters, hji]

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryMotion ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma rat (q : ℚ) : RationalConstant (q : ℝ) := ⟨q,rfl⟩

lemma nat (n : ℕ) : RationalConstant (n : ℝ) := ⟨n, by simp⟩

lemma one : RationalConstant 1 := by simpa using rat 1

lemma elementary {d : ℕ} [NeZero d] {a : ℝ} (ha : RationalConstant a) :
    Elementary (fun _ : Fin d → ℝ => a) := by
  obtain ⟨a,rfl⟩ := ha; exact Elementary.literal a

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry Set

lemma const {c : ℝ} (hc : RationalConstant c) : ElementaryCurve (fun _ => c) := hc.elementary

lemma id : ElementaryCurve (fun t => t) := Elementary.coordinate 0

lemma add {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t + g t) := Elementary.add hf hg

lemma sub {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t - g t) := Elementary.sub hf hg

lemma mul {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t * g t) := Elementary.mul hf hg

lemma div_const {f : ℝ → ℝ} (hf : ElementaryCurve f) {c : ℝ} (hc : RationalConstant c) :
    ElementaryCurve (fun t => f t / c) := by
  obtain ⟨c,rfl⟩ := hc; exact hf.div_rat c

lemma comp {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f (g t)) := Elementary.comp hf (fun x _ => g (x 0)) (fun _ => hg)

lemma transition : ElementaryCurve Real.smoothTransition := id.smoothTransition

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryMotion
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma trans {m : BoxMotion A B safe η} {n : BoxMotion B C safe η}
    (hm : ElementaryMotion m) (hn : ElementaryMotion n) (hB : RationalLayout B) :
    ElementaryMotion (m.trans n) := by
  have h₂ : ElementaryCurve (fun t => 2*t) :=
    (ElementaryCurve.const (RationalConstant.nat 2)).mul ElementaryCurve.id
  have h₂' : ElementaryCurve (fun t => 2*t-1) := h₂.sub (ElementaryCurve.const RationalConstant.one)
  constructor <;> intro i k
  · exact ((hm.1 i k).comp h₂).add ((hn.1 i k).comp h₂') |>.sub (ElementaryCurve.const (hB.1 i k))
  · exact (((hm.2 i k).comp h₂).mul ((hn.2 i k).comp h₂')).div_const (hB.2 i k)

lemma segment {a b w : ι → Space} (ha : RationalCenters a) (hb : RationalCenters b)
    (hw : RationalCenters w) (hp : ∀ i k, 0 < w i k)
    (hs : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Separated η)
    (hg : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Guarded safe) :
    ElementaryMotion (segmentMotion hp hs hg) := by
  refine ⟨?_, fun i k => ElementaryCurve.const (hw i k)⟩
  intro i k
  exact (((ElementaryCurve.const RationalConstant.one).sub ElementaryCurve.transition).mul
    (ElementaryCurve.const (ha i k))).add
    (ElementaryCurve.transition.mul (ElementaryCurve.const (hb i k)))

end BalancedTransport.Effectivity.ElementaryMotion
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma RationalCenters.update [DecidableEq ι] {a : ι → Space} (ha : RationalCenters a)
    (i : ι) {b : Space} (hb : ∀ k, RationalConstant (b k)) : RationalCenters (Function.update a i b) := by
  intro j k
  by_cases h : j = i
  · subst j; simpa using hb k
  · simpa [Function.update_of_ne h] using ha j k

lemma rational_space_update {a : Space} (ha : ∀ k, RationalConstant (a k))
    (j : Fin 3) {b : ℝ} (hb : RationalConstant b) : ∀ k, RationalConstant ((Function.update a j b) k) := by
  intro k
  by_cases he : k = j
  · subst k; simpa using hb
  · simpa [Function.update_of_ne he] using ha k

omit [Fintype ι] in
lemma rational_remaining [DecidableEq ι] {a p : ι → Space} (ha : RationalCenters a)
    (hp : RationalCenters p) (S : Finset ι) : RationalCenters (remainingCenters a p S) := by
  intro i k
  by_cases hi : i ∈ S
  · simpa [remainingCenters, hi] using ha i k
  · simpa [remainingCenters, hi] using hp i k

lemma elementary_singleSegment [DecidableEq ι] {a w : ι → Space} {D η : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (wr : RationalCenters w)
    (i : ι) (b : Space) (br : ∀ k, RationalConstant (b k))
    (hp : ∀ j k, 0 < w j k) (hw : ∀ j l k, w j k + w l k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hb : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i → ∃ k, D < |(1-r)*a i k+r*b k-a j k|)
    (hga : (BoxLayout.mk a w).Guarded safe)
    (hgb : (BoxLayout.mk (Function.update a i b) w).Guarded safe) :
    ElementaryMotion (singleSegmentMotion i b hp hw ha hb hga hgb) :=
  ElementaryMotion.segment ar (ar.update i br) wr _ _ _

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryParking ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem elementary_evacuateHighest {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (pr : RationalCenters p) (wr : RationalCenters w)
    (Hr : RationalConstant H)
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe)
    (S : Finset ι) (i : ι) (hi : i ∈ S) (hmax : ∀ j ∈ S, a j 1 ≤ a i 1) :
    ∃ m : BoxMotion ⟨remainingCenters a p S, w⟩ ⟨remainingCenters a p (S.erase i), w⟩ safe η,
      ElementaryMotion m := by
  let u := remainingCenters a p S
  let v₁ := Function.update (a i) 1 H
  let v₂ := Function.update (p i) 1 H
  have hui : u i = a i := by simp [u, remainingCenters, hi]
  have hu := remainingCenters_separated ha hcross hp S
  have hgu := remainingCenters_guarded hga hgp S
  have hv₁ : (BoxLayout.mk (Function.update u i v₁) w).Guarded safe :=
    guarded_update hgu i v₁ (by intro his; simpa [v₁] using hga i his)
  have hv₂ : (BoxLayout.mk (Function.update u i v₂) w).Guarded safe :=
    guarded_update hgu i v₂ (by intro his; simpa [v₂] using hgp i his)
  have hp₃ : (BoxLayout.mk (Function.update u i (p i)) w).Guarded safe :=
    guarded_update hgu i (p i) (fun his => hgp i his)
  have hfirst : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * u i k + r * v₁ k - u j k| := by
    intro r hr j hji
    rw [hui]
    by_cases hj : j ∈ S
    · have huj : u j = a j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact raising_gap (hmax j hj) (by linarith [hhigha i]) hr (ha i j (Ne.symm hji))
    · have huj : u j = p j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact fixed_first_gap (by simp [v₁]) (by simpa [v₁] using hcross i j)
  have hsecond : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₁) i k +
        r * v₂ k - (Function.update u i v₁) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply high_plane_gap (H := H) (by simp [v₁]) (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj] using hhigha j
    · simpa [u, remainingCenters, hj] using hhighp j
  have hthird : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₂) i k +
        r * p i k - (Function.update u i v₂) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply fixed_first_gap (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj, abs_sub_comm] using hcross j i
    · simpa [u, remainingCenters, hj] using hp i j (Ne.symm hji)
  have hsep₁ := hu.update i v₁ (fun j hji => by simpa using hfirst 1 ⟨by norm_num, le_rfl⟩ j hji)
  have hsep₂ : CenterSeparated (Function.update u i v₂) D := by
    have hh := hsep₁.update i v₂ (fun j hji => by simpa using hsecond 1 ⟨by norm_num, le_rfl⟩ j hji)
    simpa [Function.update_idem] using hh
  let m₁ := singleSegmentMotion i v₁ hwidth hsize hu hfirst hgu hv₁
  let m₂ := singleSegmentMotion i v₂ hwidth hsize hsep₁ hsecond hv₁
    (by simpa [Function.update_idem] using hv₂)
  let m₃ := singleSegmentMotion i (p i) hwidth hsize hsep₂ hthird hv₂
    (by simpa [Function.update_idem] using hp₃)
  have ur : RationalCenters u := rational_remaining ar pr S
  have v₁r : ∀ k, RationalConstant (v₁ k) := rational_space_update (ar i) 1 Hr
  have v₂r : ∀ k, RationalConstant (v₂ k) := rational_space_update (pr i) 1 Hr
  have e₁ : ElementaryMotion m₁ := elementary_singleSegment ur wr i v₁ v₁r _ _ _ _ _ _
  have e₂ : ElementaryMotion m₂ := elementary_singleSegment (ur.update i v₁r) wr i v₂ v₂r _ _ _ _ _ _
  have e₃ : ElementaryMotion m₃ := elementary_singleSegment (ur.update i v₂r) wr i (p i) (pr i) _ _ _ _ _ _
  have h₂ := Exists.intro m₂ e₂
  change ∃ m : BoxMotion ⟨Function.update u i v₁, w⟩
    ⟨Function.update (Function.update u i v₁) i v₂, w⟩ safe η, ElementaryMotion m at h₂
  rw [Function.update_idem] at h₂
  have h₃ := Exists.intro m₃ e₃
  change ∃ m : BoxMotion ⟨Function.update u i v₂, w⟩
    ⟨Function.update (Function.update u i v₂) i (p i), w⟩ safe η, ElementaryMotion m at h₃
  rw [Function.update_idem] at h₃
  obtain ⟨m₂',e₂'⟩ := h₂
  obtain ⟨m₃',e₃'⟩ := h₃
  have h : ElementaryMotion ((m₁.trans m₂').trans m₃') :=
    (e₁.trans e₂' ⟨ur.update i v₁r,wr⟩).trans e₃' ⟨ur.update i v₂r,wr⟩
  rw [remainingCenters_erase hi]
  exact ⟨_,h⟩

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.elementary_evacuateHighest := @_root_.OAI.BalancedTransport.Effectivity.elementary_evacuateHighest
