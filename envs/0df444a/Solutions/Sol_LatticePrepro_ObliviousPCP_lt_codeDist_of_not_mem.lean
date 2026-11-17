-- Prove2me | solution 1 for LatticePrepro.ObliviousPCP.lt_codeDist_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:14:28.874203+00:00
-- url     : https://prove2.me/submissions/1fd38ef1-a52d-4d57-8219-556cf7e87118

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code
import Theorems.Thm_LatticePrepro_ObliviousPCP_lt_hammingNorm_stackMap_of_solution

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ObliviousPCP end LatticePrepro.ObliviousPCP

namespace LatticePrepro

/-- The Hamming distance of vectors on a sum type is the sum of the distances of their halves. -/
lemma hammingDist_sum_elim {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (a c : α → γ) (b d : β → γ) :
    hammingDist (Sum.elim a b) (Sum.elim c d) = hammingDist a c + hammingDist b d := by
  simp only [hammingDist, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- The Hamming weight of a difference is the Hamming distance. -/
lemma hammingNorm_sub_eq_hammingDist {M : Type*} [Fintype M] {R : Type*} [AddGroup R] [DecidableEq R]
    (a b : M → R) :
    hammingNorm (a - b) = hammingDist a b := by
  simp [hammingNorm, hammingDist, sub_eq_zero]

end LatticePrepro

namespace LatticePrepro

namespace CodeFamily

variable {F : Type} [Field F] {X : Type}

lemma exists_codeDist_eq [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) : ∃ c ∈ C, hammingDist y c = codeDist y C := by
  have hne : {d | ∃ c ∈ C, hammingDist y c = d}.Nonempty := ⟨hammingDist y 0, 0, C.zero_mem, rfl⟩
  exact Nat.sInf_mem hne

lemma lt_codeDist_of_forall [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) {d : ℕ} (h : ∀ c ∈ C, d < hammingDist y c) : d < codeDist y C := by
  obtain ⟨c, hc, hd⟩ := exists_codeDist_eq y C
  rw [← hd]; exact h c hc

end CodeFamily

end LatticePrepro

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) (F : Type) [Field F]

variable {F} {B : ℕ}

/-- Membership in the code `(G₁ · ker G₀) × {0^H}`. -/
lemma mem_code_iff (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ)
    (c : P.Coord B ⊕ Fin (g * P.radius B + 1) → F) :
    c ∈ P.code E g ↔ ∃ v, P.constraintMap F v = 0 ∧ c = Sum.elim (P.stackMap E v) 0 := by
  simp only [code, Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

lemma target_of_exists (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) {x : X}
    (h : ∃ v, P.constraintMap F v = P.constraintRhs F x) :
    P.target E g x = Sum.elim (P.stackMap E h.choose) 0 := by
  simp [target, h]

lemma target_of_not_exists (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) {x : X}
    (h : ¬ ∃ v, P.constraintMap F v = P.constraintRhs F x) :
    P.target E g x = Sum.elim (0 : P.Coord B → F) (1 : Fin (g * P.radius B + 1) → F) := by
  simp [target, h]

end ObliviousPCP

end LatticePrepro

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

/-- Two words padded by zeros are at the distance of their first blocks. -/
lemma hammingDist_pad {α β : Type} [Fintype α] [Fintype β] (a a' : α → F) :
    hammingDist (Sum.elim a (0 : β → F)) (Sum.elim a' 0) = hammingNorm (a - a') := by
  rw [hammingDist_sum_elim, hammingDist_self, add_zero, hammingNorm_sub_eq_hammingDist]

/-- **Soundness of Theorem 6.4.** For `x ∉ Lang`, the target is at distance more than `g · Y`
from the code. -/
private theorem lt_codeDist_of_not_mem {Lang : Set X} {ε δ : ℝ} (hs : P.SoundnessError Lang ε)
    (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)} (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) {x : X} (hx : x ∉ Lang) :
    g * P.radius B < CodeFamily.codeDist (P.target E g x) (P.code E g) := by
  apply CodeFamily.lt_codeDist_of_forall
  intro c hc
  obtain ⟨v', hv', rfl⟩ := (P.mem_code_iff E g c).mp hc
  by_cases hex : ∃ v, P.constraintMap F v = P.constraintRhs F x
  · rw [P.target_of_exists E g hex, hammingDist_pad, ← map_sub]
    exact P.lt_hammingNorm_stackMap_of_solution hs hε hE hδ hg hx
      (by rw [map_sub, hex.choose_spec, hv', sub_zero])
  · rw [P.target_of_not_exists E g hex, hammingDist_sum_elim]
    have h1 : hammingDist (1 : Fin (g * P.radius B + 1) → F) 0 = g * P.radius B + 1 := by
      simp [hammingDist]
    omega

end ObliviousPCP

end LatticePrepro

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}
theorem solution {Lang : Set X} {ε δ : ℝ} (hs : P.SoundnessError Lang ε)
    (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)} (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) {x : X} (hx : x ∉ Lang) :
    g * P.radius B < CodeFamily.codeDist (P.target E g x) (P.code E g) :=
  @LatticePrepro.ObliviousPCP.lt_codeDist_of_not_mem X P F _ _ B Lang ε δ hs hε E hE hδ g hg x hx
