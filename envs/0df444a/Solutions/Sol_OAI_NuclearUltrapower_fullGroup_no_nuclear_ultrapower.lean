-- Prove2me | solution 1 for OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:33:36.605397+00:00
-- url     : https://prove2.me/submissions/c454887d-3c41-4d63-9917-817917e865c3

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N043
import Theorems.Thm_OAI_NuclearUltrapower_contradiction_of_initial_match
import Theorems.Thm_OAI_NuclearUltrapower_initial_match
import Theorems.Thm_OAI_NuclearUltrapower_injectiveInduced_invariant_tensor
import Theorems.Thm_OAI_NuclearUltrapower_universalGNS_injective

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NormUltrapower
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

universe u

noncomputable section
open Filter
open scoped Topology

namespace NuclearUltrapower
variable {A : Type*} [CStarAlgebra A]

/-- Both-sided approximate-unitarity is essential: no stable-finiteness or
Dedekind-finiteness is assumed for the ambient C*-algebra. -/
theorem isUnit_of_star_products {a : A} (hl : IsUnit (star a * a))
    (hr : IsUnit (a * star a)) : IsUnit a := by
  let l := Ring.inverse (star a * a) * star a
  let r := star a * Ring.inverse (a * star a)
  have hla : l * a = 1 := by
    dsimp [l]
    rw [mul_assoc, Ring.inverse_mul_cancel _ hl]
  have har : a * r = 1 := by
    dsimp [r]
    rw [← mul_assoc, Ring.mul_inverse_cancel _ hr]
  have he : l = r := by
    calc l = l * (a * r) := by rw [har, mul_one]
         _ = (l * a) * r := (mul_assoc _ _ _).symm
         _ = r := by rw [hla, one_mul]
  exact ⟨⟨a, r, har, he ▸ hla⟩, rfl⟩

attribute [local instance] OAI.NuclearUltrapower.polarSpectralOrder
attribute [local instance] OAI.NuclearUltrapower.polarSpectralOrderedRing
/-- Asymptotically unitary bounded families admit genuine unitary replacements
with norm-null difference along any filter. -/
theorem unitaryReplacement_tendsto {ι : Type*} {l : Filter ι} (a : ι → A)
    (hb : IsBoundedUnder (· ≤ ·) l (fun i => ‖a i‖))
    (hl : Tendsto (fun i => star (a i) * a i) l (𝓝 1))
    (hr : Tendsto (fun i => a i * star (a i)) l (𝓝 1)) :
    Tendsto (fun i => (unitaryReplacement (a i) : A) - a i) l (𝓝 0) := by
  have hles : ∀ᶠ i in l, IsUnit (star (a i) * a i) :=
    hl.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hres : ∀ᶠ i in l, IsUnit (a i * star (a i)) :=
    hr.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hunit : ∀ᶠ i in l, IsUnit (a i) :=
    (hles.and hres).mono (fun _ h => isUnit_of_star_products h.1 h.2)
  have hsqrt : Tendsto (fun i => CFC.sqrt (star (a i) * a i)) l (𝓝 (1 : A)) := by
    have h := (CFC.continuousOn_sqrt (A := A) 1 (by change (0 : A) ≤ 1; exact zero_le_one)).tendsto
    have hc := h.comp (tendsto_nhdsWithin_iff.mpr ⟨hl,
      Filter.Eventually.of_forall (fun i => star_mul_self_nonneg (a i))⟩)
    simpa only [Function.comp_def, CFC.sqrt_one] using hc
  have hinv : Tendsto (fun i => Ring.inverse (CFC.sqrt (star (a i) * a i))) l (𝓝 (1 : A)) := by
    have h := (NormedRing.inverse_continuousAt (1 : Aˣ)).tendsto.comp hsqrt
    simpa only [Function.comp_def, Units.val_one, Ring.inverse_one] using h
  have hz : Tendsto (fun i => Ring.inverse (CFC.sqrt (star (a i) * a i)) - 1) l (𝓝 (0 : A)) := by
    simpa using hinv.sub_const 1
  have hp := Filter.isBoundedUnder_le_mul_tendsto_zero hb hz
  apply hp.congr'
  filter_upwards [hunit] with i hi
  simp [unitaryReplacement, hi, mul_sub]

end NuclearUltrapower

namespace NuclearUltrapower
section UltrapowerDefinition
variable (B : Type u) [CStarAlgebra B] (ω : Ultrafilter ℕ)

theorem seq_bounded (x : BoundedSeq B) :
    IsBoundedUnder (· ≤ ·) (ω : Filter ℕ) (norm ∘ x) :=
  Filter.isBoundedUnder_of ⟨‖x‖, fun n => x.norm_coe_le_norm n⟩

end UltrapowerDefinition
end NuclearUltrapower

namespace NuclearUltrapower
variable {B : Type*} [CStarAlgebra B] [Nontrivial B] (ω : Ultrafilter ℕ)

omit [Nontrivial B] in
theorem normUltrapowerMk_eq_iff (x y : BoundedSeq B) :
    normUltrapowerMk B ω x = normUltrapowerMk B ω y ↔ ultraRel B ω x y :=
  Quotient.eq

omit [Nontrivial B] in
/-- The defining quotient map is surjective, with no assumed model of the quotient. -/
theorem normUltrapowerMk_surjective : Function.Surjective (normUltrapowerMk B ω) :=
  Quotient.mk_surjective

/-- 24--36, with both left and right
unitarity used. The result requires neither stable finiteness nor separability. -/
theorem unitary_lift (u : unitary (NormUltrapower B ω)) :
    ∃ x : ℕ → unitary B, normUltrapowerMk B ω (boundedUnitarySeq x) = (u : NormUltrapower B ω) := by
  obtain ⟨y, hy⟩ := normUltrapowerMk_surjective (B := B) ω u
  have hlq : normUltrapowerMk B ω (star y * y) = normUltrapowerMk B ω 1 := by
    rw [map_mul, map_star, hy, Unitary.star_mul_self_of_mem u.property, map_one]
  have hrq : normUltrapowerMk B ω (y * star y) = normUltrapowerMk B ω 1 := by
    rw [map_mul, map_star, hy, Unitary.mul_star_self_of_mem u.property, map_one]
  have hl : Tendsto (fun n => star (y n) * y n) (ω : Filter ℕ) (𝓝 1) := by
    have hh := (normUltrapowerMk_eq_iff ω _ _).mp hlq
    exact tendsto_sub_nhds_zero_iff.mp hh
  have hr : Tendsto (fun n => y n * star (y n)) (ω : Filter ℕ) (𝓝 1) := by
    have hh := (normUltrapowerMk_eq_iff ω _ _).mp hrq
    exact tendsto_sub_nhds_zero_iff.mp hh
  refine ⟨fun n => unitaryReplacement (y n), ?_⟩
  rw [← hy, normUltrapowerMk_eq_iff]
  exact unitaryReplacement_tendsto y (seq_bounded B ω y) hl hr

/-- Coordinatewise lifts preserve each fixed multiplicative relation in the
norm ultralimit. No simultaneous coordinate relations or countable intersection
of large sets are asserted. -/
theorem unitary_lift_defects {Γ : Type*} [Group Γ]
    (ρ : Γ →* unitary (NormUltrapower B ω)) (x : Γ → ℕ → unitary B)
    (hx : ∀ g, normUltrapowerMk B ω (boundedUnitarySeq (x g)) = (ρ g : NormUltrapower B ω))
    (g h : Γ) :
    Tendsto (fun n => (x g n : B) * (x h n : B) - (x (g * h) n : B))
      (ω : Filter ℕ) (𝓝 0) := by
  have he : normUltrapowerMk B ω (boundedUnitarySeq (x g) * boundedUnitarySeq (x h)) =
      normUltrapowerMk B ω (boundedUnitarySeq (x (g * h))) := by
    rw [map_mul, hx, hx, hx, map_mul, Submonoid.coe_mul]
  exact (normUltrapowerMk_eq_iff ω _ _).mp he

/-- Choice of unitary lifts, normalized at the group identity. -/
theorem exists_unitary_lifts {Γ : Type*} [Group Γ]
    (ρ : Γ →* unitary (NormUltrapower B ω)) :
    ∃ x : Γ → ℕ → unitary B, (∀ n, x 1 n = 1) ∧
      (∀ g, normUltrapowerMk B ω (boundedUnitarySeq (x g)) = (ρ g : NormUltrapower B ω)) ∧
      ∀ g h, Tendsto (fun n => (x g n : B) * (x h n : B) - (x (g * h) n : B))
        (ω : Filter ℕ) (𝓝 0) := by
  classical
  choose y hy using (fun g => unitary_lift ω (ρ g))
  let x : Γ → ℕ → unitary B := fun g => if g = 1 then fun _ => 1 else y g
  have hx : ∀ g, normUltrapowerMk B ω (boundedUnitarySeq (x g)) = (ρ g : NormUltrapower B ω) := by
    intro g
    by_cases hg : g = 1
    · subst g
      have he : boundedUnitarySeq (x 1) = (1 : BoundedSeq B) := by ext n; simp [x]
      rw [he, map_one, map_one, Submonoid.coe_one]
    · simpa [x, hg] using hy g
  exact ⟨x, fun n => by simp [x], hx, fun g h => unitary_lift_defects ω ρ x hx g h⟩

end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology ENNReal
namespace NuclearUltrapower
universe u
variable (B : Type u) [CStarAlgebra B] [Nontrivial B] (ω : Ultrafilter ℕ)

theorem normUltraToCStar_injective : Function.Injective (normUltraToCStar B ω) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((ultraRel_iff_norm B ω x y).mpr (Quotient.exact h))

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InducedApproximation
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
variable {Γ : Type u} [Group Γ]

namespace FiniteUnitaryRep

theorem Irreducible.dual {π : FiniteUnitaryRep.{u,v} Γ} (hi : π.Irreducible) :
    π.dual.Irreducible := by
  intro W hW
  change Submodule ℂ (StrongDual ℂ π) at W
  let D := InnerProductSpace.toDual ℂ π
  let V : Submodule ℂ π := {
    carrier := {x | D x ∈ W}
    zero_mem' := by simp
    add_mem' := fun hx hy => by
      change D (_+_) ∈ W
      rw [map_add]
      exact W.add_mem hx hy
    smul_mem' := fun c x hx => by
      change D (c • x) ∈ W
      rw [map_smulₛₗ]
      exact W.smul_mem (starRingEnd ℂ c) hx }
  have hV : ∀ g x, x ∈ V → π.action g x ∈ V := by
    intro g x hx
    have h := hW g (D x) hx
    change dualAction π.action g (D x) ∈ W at h
    change D (π.action g x) ∈ W
    rwa [dualAction_toDual] at h
  rcases hi V hV with hv | hv
  · left
    apply le_antisymm ?_ bot_le
    intro f hf
    obtain ⟨x,rfl⟩ := D.surjective f
    have hx : x ∈ V := hf
    rw [hv, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  · right
    apply top_unique
    intro f _
    obtain ⟨x,rfl⟩ := D.surjective f
    have hx : x ∈ V := hv ▸ Submodule.mem_top
    exact hx

/-- Contragredience is faithful on unitary equivalence classes. -/
theorem equivalent_of_dual {π τ : FiniteUnitaryRep.{u,v} Γ}
    (he : π.dual.Equivalent τ.dual) : π.Equivalent τ := by
  obtain ⟨U,hU⟩ := he
  change StrongDual ℂ π ≃ₗᵢ[ℂ] StrongDual ℂ τ at U
  let T : π ≃ₗᵢ[ℂ] τ := ((InnerProductSpace.toDual ℂ π).trans U).trans
    (InnerProductSpace.toDual ℂ τ).symm
  refine ⟨T, fun g x => ?_⟩
  apply (InnerProductSpace.toDual ℂ τ).injective
  change InnerProductSpace.toDual ℂ τ ((InnerProductSpace.toDual ℂ τ).symm
      (U (InnerProductSpace.toDual ℂ π (π.action g x)))) =
    InnerProductSpace.toDual ℂ τ (τ.action g ((InnerProductSpace.toDual ℂ τ).symm
      (U (InnerProductSpace.toDual ℂ π x))))
  rw [LinearIsometryEquiv.apply_symm_apply]
  calc
    _ = dualAction τ.action g (U (InnerProductSpace.toDual ℂ π x)) := by
      have he := hU g (InnerProductSpace.toDual ℂ π x)
      change U (dualAction π.action g (InnerProductSpace.toDual ℂ π x)) = _ at he
      rwa [dualAction_toDual] at he
    _ = _ := by
      rw [← dualAction_toDual τ.action g, LinearIsometryEquiv.apply_symm_apply]

theorem dual_aperiodic {π : FiniteUnitaryRep.{u,v} Γ} (θ : Monoid.End Γ)
    (hπ : ∀ j : ℕ, 0 < j → ¬ π.Equivalent (π.pull (θ^j))) :
    ∀ j : ℕ, 0 < j → ¬ π.dual.Equivalent (π.dual.pull (θ^j)) := by
  intro j hj he
  rw [← dual_pull] at he
  exact hπ j hj (equivalent_of_dual he)

end FiniteUnitaryRep
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_GroupObstruction
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower

/-- A faithful unital representation of a nonzero algebra has nonzero Hilbert space. -/
theorem faithful_hilbert_nontrivial {B E : Type*} [CStarAlgebra B] [Nontrivial B]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (hρ : Function.Injective ρ) : Nontrivial E := by
  by_contra h
  have : Subsingleton E := not_nontrivial_iff_subsingleton.mp h
  exact (zero_ne_one : (0 : B) ≠ 1) (hρ (Subsingleton.elim _ _))

section Obstruction
variable {Γ Δ B : Type} [Group Γ] [Group Δ] [CStarAlgebra B] [Nontrivial B]
  (f : Γ →* Δ) (hf : Function.Injective f)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)]
  (t : Δ) (ht : ∀ g, f (θ g) * t = t * f g)
  (S : Finset Γ) (hSne : S.Nonempty) (hS : Subgroup.closure (S : Set Γ) = ⊤)
  (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
  (hgap : HasKazhdanGap.{0,0} S κ)
  (π : FiniteUnitaryRep.{0,0} Γ) (hirr : π.Irreducible)
  (haper : ∀ p : ℕ, 0 < p → ¬ π.Equivalent (π.pull (θ^p)))

include hf hθ ht hSne hS hκ0 hκ hgap hirr haper in
/-- The spectral obstruction for an injective
ascending subgroup in the exact ambient group, without assuming an initial
match or a coordinate representation. -/
theorem fullGroup_no_nuclear_ultrapower_oai (hB : IsNuclear.{0,0} B)
    (ω : Ultrafilter ℕ) (hω : IsFree ω) :
    ¬ ∃ φ : FullGroupModel.Full Δ →⋆ₐ[ℂ] NormUltrapower B ω,
      Function.Injective φ := by
  classical
  rintro ⟨φ,hφ⟩
  let ρ := universalGNS (A := B)
  have hρ : Function.Injective ρ := universalGNS_injective
  let : Nontrivial (UniversalGNS B) := faithful_hilbert_nontrivial ρ hρ
  let ι := FullGroupModel.inclusion Δ
  let φu : FullGroupModel.Full Δ →⋆* NormUltrapower B ω :=
    { φ.toMonoidHom with map_star' := map_star φ }
  let r : Δ →* unitary (NormUltrapower B ω) :=
    (Unitary.map φu).toMonoidHom.comp ι
  obtain ⟨u,hu1,hu,hmul⟩ := exists_unitary_lifts ω r
  have hmul' (g h : Δ) : Tendsto
      (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
        (ω : Filter ℕ) (𝓝 0) := by
    simpa only [norm_sub_rev, norm_zero] using (hmul g h).norm
  let φ' := (normUltraToCStar B ω).comp φ
  have hφ' : Function.Injective φ' := (normUltraToCStar_injective B ω).comp hφ
  let σ := injectiveInduced f hf π
  let ψ := FullGroupModel.modelMap Δ
    (Unitary.linearIsometryEquiv.symm.toMonoidHom.comp σ)
  have hψ (g : Γ) : ψ (ι (f g)) = (σ (f g) : InjectiveInducedSpace f π →L[ℂ] _) := by
    exact FullGroupModel.modelMap_generator Δ _ (f g)
  have hu' (g : Γ) : φ' (ι (f g)) = VariableUltra.mk (fun _ : ℕ => B) ω
      (VariableUltra.unitarySequence (fun _ : ℕ => B) (u (f g))) := by
    have h := congrArg (normUltraToCStar B ω) (hu (f g))
    have hr (d : Δ) : (r d : NormUltrapower B ω) = φ (ι d) := rfl
    rw [hr] at h
    simpa only [normUltraToCStar_mk, boundedSeqToLp_unitary, φ',
      StarAlgHom.comp_apply] using h.symm
  obtain ⟨z,hz0,hz⟩ := injectiveInduced_invariant_tensor f hf π
  let a : ℝ := min (κ/2) (κ^2 / (8 * (S.card : ℝ)))
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSne
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have ha : a < κ := (min_le_left _ _).trans_lt (by linarith)
  have ha' : a < κ^2 / (4 * (S.card : ℝ)) := by
    have hk2 : 0 < κ^2 := sq_pos_of_pos hκ0
    exact (min_le_right _ _).trans_lt (by
      apply div_lt_div_of_pos_left hk2 (by positivity)
      linarith)
  have hm := initial_match ρ hρ S ω φ' hφ' (fun g => (ι (f g) : FullGroupModel.Full Δ))
    (fun g => u (f g)) hu' ψ (fun g => σ (f g)) hψ π.dual a ha0
    (ha.le.trans hκ) z hz0 (fun s _ => hz s)
  exact contradiction_of_initial_match ρ f θ hθ t S u ω κ a hB hSne hκ0 hκ hgap hS
    ha ha0 ha' ht (fun n => by simpa only [Finset.coe_singleton] using hω {n}) hu1 hmul'
    π.dual hirr.dual (FiniteUnitaryRep.dual_aperiodic θ haper) hm
end Obstruction
end NuclearUltrapower
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower_oai := @OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower_oai
