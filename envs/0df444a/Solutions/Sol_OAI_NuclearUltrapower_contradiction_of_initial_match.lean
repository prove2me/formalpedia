-- Prove2me | solution 1 for OAI.NuclearUltrapower.contradiction_of_initial_match
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:32:52.380799+00:00
-- url     : https://prove2.me/submissions/8998919e-859a-4549-9757-13ac121295ef

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N043
import Theorems.Thm_OAI_NuclearUltrapower_matchClasses_finite
import Theorems.Thm_OAI_NuclearUltrapower_uniform_predecessors

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteRepresentations
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter
noncomputable section
open scoped InnerProductSpace

namespace NuclearUltrapower

attribute [instance] FiniteUnitaryRep.normed FiniteUnitaryRep.inner
  FiniteUnitaryRep.complete FiniteUnitaryRep.finite FiniteUnitaryRep.nontrivial

variable {Γ : Type u} [Group Γ]

namespace FiniteUnitaryRep

theorem Equivalent.embeds {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) : π.Embeds τ := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T.toLinearIsometry, hT⟩

theorem Embeds.pull {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (θ : Monoid.End Γ) : (π.pull θ).Embeds (τ.pull θ) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun g => hT (θ g)⟩

theorem Equivalent.pull {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) (θ : Monoid.End Γ) : (π.pull θ).Equivalent (τ.pull θ) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun g => hT (θ g)⟩

/-- Equidimensional subrepresentations are unitary equivalences. -/
theorem Embeds.equivalent_of_finrank_eq {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (hd : Module.finrank ℂ π = Module.finrank ℂ τ) : π.Equivalent τ := by
  obtain ⟨T, hT⟩ := h
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp T.injective
  exact ⟨LinearIsometryEquiv.ofSurjective T hs, hT⟩

/-- Irreducibility is preserved under unitary equivalence. -/
theorem Equivalent.irreducible {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) (hπ : π.Irreducible) : τ.Irreducible := by
  obtain ⟨T, hT⟩ := h
  intro W hW
  have hi : ∀ g x, x ∈ W.comap T.toLinearEquiv.toLinearMap →
      π.action g x ∈ W.comap T.toLinearEquiv.toLinearMap := by
    intro g x hx
    change T (π.action g x) ∈ W
    rw [hT]
    exact hW g (T x) hx
  rcases hπ _ hi with hb | ht
  · left
    apply bot_unique
    intro y hy
    change y = 0
    obtain ⟨x, rfl⟩ := T.surjective y
    have hx : x ∈ W.comap T.toLinearEquiv.toLinearMap := hy
    rw [hb, Submodule.mem_bot] at hx
    simp [hx]
  · right
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := T.surjective y
    have hx : x ∈ W.comap T.toLinearEquiv.toLinearMap := by rw [ht]; trivial
    exact hx

/-- A nonzero subrepresentation of an irreducible representation is the whole. -/
theorem Embeds.equivalent_of_irreducible {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (hτ : τ.Irreducible) : π.Equivalent τ := by
  obtain ⟨T, hT⟩ := h
  have hr : ∀ g x, x ∈ T.toLinearMap.range → τ.action g x ∈ T.toLinearMap.range := by
    rintro g x ⟨y, rfl⟩
    exact ⟨π.action g y, hT g y⟩
  rcases hτ _ hr with hb | ht
  · have hz : T.toLinearMap = 0 := LinearMap.range_eq_bot.mp hb
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    have hzx : T x = 0 := congrArg (fun L : π →ₗ[ℂ] τ => L x) hz
    have := T.injective (show T x = T 0 by rw [hzx, map_zero])
    exact False.elim (hx this)
  · exact ⟨LinearIsometryEquiv.ofSurjective T (LinearMap.range_eq_top.mp ht), hT⟩

/-- If a deeper pullback is irreducible, every preceding pullback is irreducible. -/
theorem irreducible_of_pull {π : FiniteUnitaryRep.{u,v} Γ} (θ : Monoid.End Γ)
    (h : (π.pull θ).Irreducible) : π.Irreducible := by
  intro W hW
  exact h W (fun g => hW (θ g))

/-- Periodicity forces *every* positive pullback to remain irreducible, the
critical step often missed when a predecessor chain has a nonempty tail. -/
theorem irreducible_pull_of_periodic {π : FiniteUnitaryRep.{u,v} Γ}
    (hπ : π.Irreducible) (θ : Monoid.End Γ) {p : ℕ} (hp : 0 < p)
    (he : π.Equivalent (π.pull (θ ^ p))) (j : ℕ) : (π.pull (θ ^ j)).Irreducible := by
  have hit (k : ℕ) : π.Equivalent (π.pull (θ ^ (p * k))) := by
    induction k with
    | zero => simpa using π.equivalent_refl
    | succ k ih =>
        have ht := he.pull (θ ^ (p * k))
        rw [pull_pull, ← pow_add] at ht
        simpa [Nat.mul_succ, Nat.add_comm] using ih.trans ht
  have hj : j ≤ p * j := Nat.le_mul_of_pos_left j hp
  have hi := (hit j).irreducible hπ
  have heq : (π.pull (θ ^ j)).pull (θ ^ (p * j - j)) = π.pull (θ ^ (p * j)) := by
    rw [pull_pull, ← pow_add, Nat.add_sub_of_le hj]
  rw [← heq] at hi
  exact irreducible_of_pull _ hi

/-- Source lem:finite-predecessor-cycle, expressed using any finite list of
representatives. Duplicates are harmless; no bijective predecessor selection is
assumed, and the possibly nonempty tail is fully accounted for. -/
theorem finite_predecessor_cycle {ι : Type*} [Finite ι]
    (π : ι → FiniteUnitaryRep.{u,v} Γ) (hπ : ∀ i, (π i).Irreducible)
    (θ : Monoid.End Γ) (hprev : ∀ i, ∃ j, (π i).Embeds ((π j).pull θ)) (i : ι) :
    ∃ p : ℕ, 0 < p ∧ (π i).Equivalent ((π i).pull (θ ^ p)) := by
  classical
  let f : ι → ι := fun i => (hprev i).choose
  have hf (i : ι) : (π i).Embeds ((π (f i)).pull θ) := (hprev i).choose_spec
  have hc (n : ℕ) (i : ι) : (π i).Embeds ((π (f^[n] i)).pull (θ ^ n)) := by
    induction n generalizing i with
    | zero => simpa using (π i).embeds_refl
    | succ n ih =>
        have ht := (hf i).trans ((ih (f i)).pull θ)
        simpa only [pull_pull, ← pow_succ, Function.iterate_succ_apply] using ht
  have hex : ∃ l m : ℕ, l < m ∧ f^[l] i = f^[m] i := by
    obtain ⟨l, m, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] i)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨l, m, hlt, heq⟩
    · exact ⟨m, l, hlt, heq.symm⟩
  obtain ⟨l, m, hlm, heq⟩ := hex
  let p := m - l
  have hp : 0 < p := Nat.sub_pos_of_lt hlm
  have heq' : f^[p] (f^[l] i) = f^[l] i := by
    rw [← Function.iterate_add_apply]
    dsimp [p]
    rw [Nat.sub_add_cancel hlm.le, ← heq]
  have hb : (π (f^[l] i)).Embeds ((π (f^[l] i)).pull (θ ^ p)) := by
    simpa only [heq'] using hc p (f^[l] i)
  have he := hb.equivalent_of_finrank_eq rfl
  have hi := irreducible_pull_of_periodic (hπ (f^[l] i)) θ hp he l
  have hin := (hc l i).equivalent_of_irreducible hi
  have hmid := he.pull (θ ^ l)
  have hend := (hin.pull (θ ^ p)).symm
  simp only [pull_pull, ← pow_add] at hmid hend
  rw [Nat.add_comm l p] at hend
  exact ⟨p, hp, hin.trans (hmid.trans hend)⟩

end FiniteUnitaryRep
end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Predecessors
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
universe u v
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)
  (a : ℝ) (θ : Monoid.End Γ)

omit [Nontrivial E] in
/-- The finite predecessor graph forces periodicity of every matched irreducible,
including the initial vertex even if it lies on a nonempty tail. -/
theorem periodic_of_finite_matches
    (hf : (matchClasses ρ S u a).Finite)
    (hp : ∀ π : FiniteUnitaryRep.{u,v} Γ, π.Irreducible → Matches ρ S u a π →
      ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ Matches ρ S u a τ ∧ π.Embeds (τ.pull θ))
    (π : FiniteUnitaryRep.{u,v} Γ) (hπ : π.Irreducible) (hm : Matches ρ S u a π) :
    ∃ p : ℕ, 0 < p ∧ π.Equivalent (π.pull (θ^p)) := by
  classical
  let D := matchClasses ρ S u a
  let : Finite D := hf.to_subtype
  have hex (q : D) : ∃ τ : FiniteUnitaryRep.{u,v} Γ,
      τ.Irreducible ∧ Matches ρ S u a τ ∧
      Quotient.mk (FiniteUnitaryRep.classSetoid Γ) τ = q.1 := q.2
  choose σ hirr hmatch hclass using hex
  have hprev (q : D) : ∃ r : D, (σ q).Embeds ((σ r).pull θ) := by
    obtain ⟨τ,ht,hmt,he⟩ := hp (σ q) (hirr q) (hmatch q)
    let r : D := ⟨Quotient.mk (FiniteUnitaryRep.classSetoid Γ) τ,τ,ht,hmt,rfl⟩
    have hτ : τ.Equivalent (σ r) := Quotient.exact (hclass r).symm
    exact ⟨r,he.trans (hτ.embeds.pull θ)⟩
  let q : D := ⟨Quotient.mk (FiniteUnitaryRep.classSetoid Γ) π,π,hπ,hm,rfl⟩
  have he : π.Equivalent (σ q) := Quotient.exact (hclass q).symm
  obtain ⟨p,hp,hh⟩ := FiniteUnitaryRep.finite_predecessor_cycle σ hirr θ hprev q
  exact ⟨p,hp,he.trans (hh.trans (he.pull (θ^p)).symm)⟩
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section Predecessors
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)] (t : Δ)
  (S : Finset Γ) (u : Δ → ℕ → unitary B) (ω : Ultrafilter ℕ)

include hθ in
/-- The finite-match mechanism excludes an aperiodic irrep appearing in the
ultrapower spectral support. -/
theorem contradiction_of_initial_match_oai (κ a : ℝ)
    (hB : IsNuclear.{u,u} B) (hSne : S.Nonempty)
    (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,u} S κ) (hS : Subgroup.closure (S : Set Γ) = ⊤)
    (ha : a < κ) (ha0 : 0 < a) (ha' : a < κ^2 / (4 * (S.card : ℝ)))
    (ht : ∀ g, f (θ g) * t = t * f g)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (π : FiniteUnitaryRep.{u,u} Γ) (hirr : π.Irreducible)
    (haper : ∀ p : ℕ, 0 < p → ¬ π.Equivalent (π.pull (θ^p)))
    (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u (f g) n) a π) : False := by
  have hp := uniform_predecessors ρ f θ hθ t S u ω κ a hgap hS ha ha0 ht hω h1 hmul π hirr
  obtain ⟨n,hn,hmn⟩ := (hp.and hm).exists
  have hfin := matchClasses_finite ρ S (fun g => u (f g) n) ω hB κ a hSne hκ0 hκ hgap ha' hω
  obtain ⟨p,hp,he⟩ := periodic_of_finite_matches ρ S (fun g => u (f g) n) a θ hfin hn π hirr hmn
  exact haper p hp he

end Predecessors
end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.NuclearUltrapower.contradiction_of_initial_match_oai.{u} := @OAI.NuclearUltrapower.contradiction_of_initial_match_oai.{u}
