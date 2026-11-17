-- Prove2me | solution 1 for LatticePrepro.ObliviousPCP.codeDist_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:11:22.819817+00:00
-- url     : https://prove2.me/submissions/375e6f4e-cb89-4302-b57e-d342a74e3a1b

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code

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

lemma codeDist_le [DecidableEq F] {M : Type} [Fintype M] (y : M → F) (C : Submodule F (M → F))
    {c : M → F} (hc : c ∈ C) : codeDist y C ≤ hammingDist y c :=
  Nat.sInf_le ⟨c, hc, rfl⟩

end CodeFamily

end LatticePrepro

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X)

/-- The number of random strings is `2^ρ`. -/
lemma card_rand : Fintype.card P.Rand = 2 ^ P.ρ := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end ObliviousPCP

end LatticePrepro

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) (F : Type) [Field F]

lemma constraintMap_apply (v : P.Views → F) (r : P.Rand) (V : P.Pred r) :
    P.constraintMap F v ⟨r, V⟩ = ∑ w : P.View r, if w.pred = V then v ⟨r, w⟩ else 0 := rfl

lemma constraintRhs_apply (x : X) (r : P.Rand) (V : P.Pred r) :
    P.constraintRhs F x ⟨r, V⟩ = if V = P.verifier x r then 1 else 0 := rfl

lemma restrict_apply (u : Fin P.ℓ) (a : P.Alphabet) (v : P.Views → F) (i : P.Views) :
    P.restrict F u a v i = if P.Hits u a i then v i else 0 := rfl

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

end ObliviousPCP

end LatticePrepro

namespace LatticePrepro

/-- The Hamming weight of a vector on a product type is the sum of the weights of its slices. -/
lemma hammingNorm_prod {α β γ : Type*} [Fintype α] [Fintype β] [Zero γ] [DecidableEq γ]
    (f : α × β → γ) : hammingNorm f = ∑ a, hammingNorm fun b => f (a, b) := by
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_prod_type]

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

/-- The weight of `G₁ · v` (equation (29)), with the copies indexed by the queries `(r, j)`. -/
lemma hammingNorm_stackMap (E : (P.Views → F) →ₗ[F] (Fin B → F)) (v : P.Views → F) :
    hammingNorm (P.stackMap E v) =
      ∑ r : P.Rand, ∑ j : Fin P.q, ∑ a : P.Alphabet,
        hammingNorm (E (P.restrict F (P.query r j) a v)) := by
  rw [hammingNorm_prod]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hammingNorm_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hammingNorm_prod]
  rfl

/-- Two words padded by zeros are at the distance of their first blocks. -/
lemma hammingDist_pad {α β : Type} [Fintype α] [Fintype β] (a a' : α → F) :
    hammingDist (Sum.elim a (0 : β → F)) (Sum.elim a' 0) = hammingNorm (a - a') := by
  rw [hammingDist_sum_elim, hammingDist_self, add_zero, hammingNorm_sub_eq_hammingDist]

section Completeness

variable (x : X) (π : P.Proof) (hπ : ∀ r, P.Accepts x r π)

/-- The accepting view `(V_{x,r}, π|_{I_r})` of a proof that is accepted for every random
string. -/
def honestView (r : P.Rand) : P.View r :=
  ⟨(P.verifier x r, fun j => π (P.query r j)), hπ r, fun _ _ h => congrArg π h⟩

/-- The honest solution: the indicator vector of the views `(V_{x,r}, π|_{I_r})`. -/
def honest (F : Type) [Field F] : P.Views → F :=
  fun i => if i.2 = P.honestView x π hπ i.1 then 1 else 0

omit [DecidableEq F] in
/-- The honest solution satisfies the constraints (27). -/
lemma constraintMap_honest :
    P.constraintMap F (P.honest x π hπ F) = P.constraintRhs F x := by
  funext ⟨r, V⟩
  rw [constraintMap_apply, constraintRhs_apply, Finset.sum_eq_single (P.honestView x π hπ r)]
  · have h1 : (P.honestView x π hπ r).pred = P.verifier x r := rfl
    have h2 : P.honest x π hπ F ⟨r, P.honestView x π hπ r⟩ = 1 := if_pos rfl
    rw [h1, h2]
    by_cases h : P.verifier x r = V
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro w _ hw
    have h2 : P.honest x π hπ F ⟨r, w⟩ = 0 := if_neg hw
    rw [h2, ite_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [DecidableEq F] in
/-- Every view in the support of the honest solution has answer `π(u)` at each of its queried
locations `u`, so `v^{u,a} = 0` for `a ≠ π(u)`. -/
lemma restrict_honest_eq_zero {u : Fin P.ℓ} {a : P.Alphabet} (ha : a ≠ π u) :
    P.restrict F u a (P.honest x π hπ F) = 0 := by
  funext i
  rw [restrict_apply]
  by_cases h : P.Hits u a i
  · rw [if_pos h]
    obtain ⟨j, hj, hja⟩ := h
    refine if_neg fun hi => ha ?_
    rw [← hja, hi, ← hj]
    rfl
  · rw [if_neg h]
    rfl

/-- The honest solution has weight at most `Y`. -/
lemma hammingNorm_stackMap_honest_le (E : (P.Views → F) →ₗ[F] (Fin B → F)) :
    hammingNorm (P.stackMap E (P.honest x π hπ F)) ≤ P.radius B := by
  rw [P.hammingNorm_stackMap]
  calc ∑ r : P.Rand, ∑ j : Fin P.q, ∑ a : P.Alphabet,
        hammingNorm (E (P.restrict F (P.query r j) a (P.honest x π hπ F)))
      ≤ ∑ _r : P.Rand, ∑ _j : Fin P.q, B := by
        refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun j _ => ?_
        rw [Finset.sum_eq_single (π (P.query r j))]
        · exact hammingNorm_le_card_fintype.trans_eq (Fintype.card_fin B)
        · intro a _ ha
          rw [P.restrict_honest_eq_zero x π hπ ha, map_zero, hammingNorm_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = P.radius B := by
        simp only [Finset.sum_const, Finset.card_univ, P.card_rand, Fintype.card_fin, smul_eq_mul,
          radius]
        ring

end Completeness

/-- **Completeness of Theorem 6.4.** For `x ∈ Lang`, the target is within distance `Y` of the
code. -/
private theorem codeDist_le_of_mem {Lang : Set X} (hc : P.PerfectlyComplete Lang)
    (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) {x : X} (hx : x ∈ Lang) :
    CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B := by
  obtain ⟨π, hπ⟩ := hc x hx
  have hsol : P.constraintMap F (P.honest x π hπ F) = P.constraintRhs F x :=
    P.constraintMap_honest x π hπ
  have hex : ∃ v, P.constraintMap F v = P.constraintRhs F x := ⟨_, hsol⟩
  have hmem : Sum.elim (P.stackMap E (hex.choose - P.honest x π hπ F)) 0 ∈ P.code E g := by
    rw [P.mem_code_iff]
    exact ⟨_, by rw [map_sub, hex.choose_spec, hsol, sub_self], rfl⟩
  calc CodeFamily.codeDist (P.target E g x) (P.code E g)
      ≤ hammingDist (P.target E g x)
          (Sum.elim (P.stackMap E (hex.choose - P.honest x π hπ F)) 0) :=
        CodeFamily.codeDist_le _ _ hmem
    _ = hammingNorm (P.stackMap E (P.honest x π hπ F)) := by
        rw [P.target_of_exists E g hex, hammingDist_pad, ← map_sub, sub_sub_cancel]
    _ ≤ P.radius B := P.hammingNorm_stackMap_honest_le x π hπ E

end ObliviousPCP

end LatticePrepro

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}
theorem solution {Lang : Set X} (hc : P.PerfectlyComplete Lang)
    (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) {x : X} (hx : x ∈ Lang) :
    CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B :=
  @LatticePrepro.ObliviousPCP.codeDist_le_of_mem X P F _ _ B Lang hc E g x hx
