-- Prove2me | solution 1 for OAI.Saxl.Balance.balance_support_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:10:59.824323+00:00
-- url     : https://prove2.me/submissions/842f7fce-30b2-4806-a4e9-fd8442627a6a

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/

lemma averagedMap_apply {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) (x : X) :
    averagedMap ρ σ f x = ∑ g : G, σ g (f (ρ g⁻¹ x)) := by
  simp only [averagedMap, Representation.IntertwiningMap.coe_mk, LinearMap.sum_apply,
    LinearMap.comp_apply]

/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
theorem sector_average_nonzero {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (H : Subgroup G) (f : X →ₗ[ℂ] Y) (hf : f ≠ 0)
    (he : ∀ g ∈ H, ∀ x, f (ρ g x) = σ g (f x))
    (P : Y →ₗ[ℂ] Y) (hP : ∀ x, P (f x) = f x)
    (hkill : ∀ g ∉ H, ∀ x, P (σ g (f x)) = 0) :
    averagedMap ρ σ f ≠ 0 := by
  classical
  have hproj (x : X) : P (averagedMap ρ σ f x) =
      ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) • f x := by
    rw [averagedMap_apply, map_sum]
    have hh (g : G) : P (σ g (f (ρ g⁻¹ x))) = if g ∈ H then f x else 0 := by
      by_cases hg : g ∈ H
      · rw [ite_eq_left hg, ← he g hg, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        exact hP x
      · rw [ite_eq_right hg]
        exact hkill g hg _
    simp only [hh]
    simp [Finset.sum_ite, Nat.cast_smul_eq_nsmul]
  have hc : ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, by simp⟩)
  intro hz
  apply hf
  ext x
  have heq := hproj x
  rw [hz] at heq
  change P 0 = _ at heq
  rw [map_zero] at heq
  exact (smul_eq_zero.mp heq.symm).resolve_left hc

open scoped MonoidAlgebra

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Separation. -/

section

noncomputable section
namespace Saxl

lemma equal_sets_of_card_sum_gap {X : Type*} [DecidableEq X]
    (A B : Finset X) (z : X → ℤ) (hc : A.card = B.card)
    (hz : ∑ x ∈ A, z x = ∑ x ∈ B, z x)
    (hgap : ∀ x ∈ A \ B, ∀ y ∈ B \ A, z y < z x) : A = B := by
  classical
  have he := Finset.card_sdiff_comm hc
  let e : ↥(A \ B) ≃ ↥(B \ A) := Finset.equivOfCardEq he
  have hsum : ∑ x ∈ A \ B, z x = ∑ x ∈ B \ A, z x := by
    have h₁ := Finset.sum_sdiff_eq_sub (f := z) (Finset.inter_subset_left (s₁ := A) (s₂ := B))
    have h₂ := Finset.sum_sdiff_eq_sub (f := z) (Finset.inter_subset_right (s₁ := A) (s₂ := B))
    simp only [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] at h₁ h₂
    rw [h₁, h₂, hz]
  have hn : A \ B = ∅ := by
    by_contra hn
    have hs : (Finset.univ : Finset ↥(A \ B)).Nonempty := by
      obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      exact ⟨⟨x,hx⟩,Finset.mem_univ _⟩
    have hh : (∑ x : ↥(A \ B), z (e x)) < ∑ x : ↥(A \ B), z x := by
      apply Finset.sum_lt_sum_of_nonempty hs
      intro x hx
      exact hgap x.val x.property (e x).val (e x).property
    rw [Equiv.sum_comp e (fun y : ↥(B \ A) => z y),
      Finset.sum_coe_sort, Finset.sum_coe_sort, hsum] at hh
    exact lt_irrefl _ hh
  exact Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp hn) hc.ge

theorem ordered_output_fibers_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (a b : X → ℕ) (z : X → ℤ)
    (ho : ∀ x ∈ s, ∀ y ∈ s, b x < b y → z x < z y)
    (hc : ∀ k, (s.filter (fun x => a x = k)).card =
      (s.filter (fun x => b x = k)).card)
    (hz : ∀ k, ∑ x ∈ s.filter (fun x => a x = k), z x =
      ∑ x ∈ s.filter (fun x => b x = k), z x) :
    ∀ k, s.filter (fun x => a x = k) = s.filter (fun x => b x = k) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply equal_sets_of_card_sum_gap _ _ z (hc k) (hz k)
    intro x hx y hy
    obtain ⟨hxA,hxB⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyB,hyA⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hxs,hxa⟩ := Finset.mem_filter.mp hxA
    obtain ⟨hys,hyb⟩ := Finset.mem_filter.mp hyB
    have hxne : b x ≠ k := by
      intro hh
      exact hxB (Finset.mem_filter.mpr ⟨hxs,hh⟩)
    have hxge : k ≤ b x := by
      by_contra hh
      have hh' : b x < k := Nat.lt_of_not_ge hh
      have hi := ih (b x) hh'
      have hx' : x ∈ s.filter (fun w => a w = b x) := by
        rw [hi]
        exact Finset.mem_filter.mpr ⟨hxs,rfl⟩
      have ha := (Finset.mem_filter.mp hx').2
      omega
    exact ho y hys x hxs (by omega)

lemma ordered_output_labels_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (a b : X → ℕ) (z : X → ℤ)
    (ho : ∀ x ∈ s, ∀ y ∈ s, b x < b y → z x < z y)
    (hc : ∀ k, (s.filter (fun x => a x = k)).card =
      (s.filter (fun x => b x = k)).card)
    (hz : ∀ k, ∑ x ∈ s.filter (fun x => a x = k), z x =
      ∑ x ∈ s.filter (fun x => b x = k), z x) :
    ∀ x ∈ s, a x = b x := by
  intro x hx
  have he := ordered_output_fibers_eq s a b z ho hc hz (b x)
  have hh : x ∈ s.filter (fun w => a w = b x) := by
    rw [he]
    exact Finset.mem_filter.mpr ⟨hx,rfl⟩
  exact (Finset.mem_filter.mp hh).2

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OneExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma intertwining_comp_ne_zero {G X Y Z : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap σ τ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) : F.comp f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hh := congrArg (fun H => H x) hz
  exact hh.trans (map_zero F).symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Projection. -/

section

noncomputable section
namespace Saxl.Balance

lemma balanceWords_iff_components {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (w : Fin n → Fin d)
    (hw : ∀ k, ∑ i ∈ Finset.univ.filter (fun i => c i = k), z (w i) = σ k) :
    balanceWords c A label z σ w ↔ componentWords c A label w := by
  classical
  constructor
  · rintro ⟨hA,hcs⟩
    refine ⟨hA,fun i => ?_⟩
    exact (ordered_output_labels_eq Finset.univ c (fun i => label (w i))
      (fun i => z (w i)) (fun i hi j hj hh => ho _ _ (hA i) (hA j) hh)
      (fun k => (hcs k).1.symm) (fun k => (hw k).trans (hcs k).2.symm)
      i (Finset.mem_univ i)).symm
  · rintro ⟨hA,hl⟩
    refine ⟨hA, fun k => ?_⟩
    simp only [hl]
    exact ⟨True.intro,hw k⟩

theorem balance_projection_eq {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (x : WordSpace n d) (hx : FixedComponentSums c z σ x) :
    coordinateProjection (balanceWords c A label z σ) x =
      coordinateProjection (componentWords c A label) x := by
  classical
  funext w
  by_cases hw : x w = 0
  · simp only [coordinateProjection_apply, hw, ite_self]
  · simp only [coordinateProjection_apply,
      balanceWords_iff_components c A label z σ ho w (hx w hw)]

theorem component_projection_mem {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (W : Subrepresentation (wordRep n d)) (x : WordSpace n d)
    (hxW : x ∈ W) (hx : FixedComponentSums c z σ x) :
    coordinateProjection (componentWords c A label) x ∈
      ((invariantCoordinateProjection (balanceWords c A label z σ)
        (balanceWords_invariant c A label z σ)).comp (subrepInclusion W)).range := by
  refine ⟨⟨x,hxW⟩, ?_⟩
  exact balance_projection_eq c A label z σ ho x hx

theorem components_support_transfer {n d : ℕ} {X : Type*}
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ fiberGroup c, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ W)
    (hs : ∀ x w, f x w ≠ 0 → componentWords c A label w) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  classical
  let P := coordinateProjection (componentWords c A label)
  have hP (x) : P (f x) = f x := by
    ext w
    change (if componentWords c A label w then f x w else 0) = _
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp (fun hh => h (hs x w hh))).symm
  have hk (g : Equiv.Perm (Fin n)) (hg : g ∉ fiberGroup c) (x) :
      P (wordRep n d g (f x)) = 0 := by
    ext w
    change (if componentWords c A label w then f x (w ∘ g) else 0) = 0
    split_ifs with hw
    · by_contra hn
      have hh := hs x (w ∘ g) hn
      apply hg
      intro i
      exact (hw.2 (g i)).symm.trans (hh.2 i)
    · rfl
  let F := averagedMap ρ (wordRep n d) f
  have hF : F ≠ 0 := sector_average_nonzero ρ (wordRep n d) (fiberGroup c) f hf he P hP hk
  have hmem (x) : F x ∈ W := by
    rw [show F x = _ from averagedMap_apply ρ (wordRep n d) f x]
    apply Submodule.sum_mem
    intro g hg
    exact W.apply_mem_toSubmodule g (hm _)
  let T : Representation.IntertwiningMap ρ W.toRepresentation :=
    { toLinearMap := F.toLinearMap.codRestrict _ hmem
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  refine ⟨T, ?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun l => l x) hz)

theorem balance_support_transfer {n d : ℕ} {X : Type*}
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (L : X →ₗ[ℂ] WordSpace n d)
    (hm : ∀ x, L x ∈ W) (hσ : ∀ x, FixedComponentSums c z σ (L x))
    (hf : (coordinateProjection (componentWords c A label)).comp L ≠ 0)
    (he : ∀ g ∈ fiberGroup c, ∀ x,
      coordinateProjection (componentWords c A label) (L (ρ g x)) =
      wordRep n d g (coordinateProjection (componentWords c A label) (L x))) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  classical
  let P := (invariantCoordinateProjection (balanceWords c A label z σ)
    (balanceWords_invariant c A label z σ)).comp (subrepInclusion W)
  let f := (coordinateProjection (componentWords c A label)).comp L
  have hmem (x) : f x ∈ P.range :=
    component_projection_mem c A label z σ ho W (L x) (hm x) (hσ x)
  have hsector (x w) (hw : f x w ≠ 0) : componentWords c A label w := by
    by_contra hn
    exact hw (by change (if componentWords c A label w then L x w else 0) = 0; rw [ite_eq_right hn])
  obtain ⟨T,hT⟩ := components_support_transfer ρ P.range c A label f hf he hmem hsector
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range P P.range le_rfl
  refine ⟨i.comp T, ?_⟩
  exact intertwining_comp_ne_zero i hi T hT

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

theorem balance_support_of_surjective_oai {n d : ℕ} {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (φ : G →* fiberGroup c) (hφ : Function.Surjective φ)
    (τ : Representation ℂ G Y)
    (L : Y →ₗ[ℂ] WordSpace n d)
    (hm : ∀ y, L y ∈ W) (hs : ∀ y, FixedComponentSums c z σ (L y))
    (T : Representation.IntertwiningMap τ
      ((wordRep n d).comp ((fiberGroup c).subtype.comp φ)))
    (hT : Function.Injective T)
    (he : ∀ y, coordinateProjection (componentWords c A label) (L y) = T y)
    (f : Representation.IntertwiningMap
      (ρ.comp ((fiberGroup c).subtype.comp φ)) τ) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  let K := L.comp f.toLinearMap
  have hK : (coordinateProjection (componentWords c A label)).comp K ≠ 0 := by
    intro h0
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply hT
    change T (f x) = T 0
    rw [map_zero, ← he]
    exact LinearMap.congr_fun h0 x
  apply balance_support_transfer ρ W c A label z σ ho K
    (fun x => hm (f x)) (fun x => hs (f x)) hK
  intro g hg x
  obtain ⟨a,ha⟩ := hφ ⟨g,hg⟩
  have hval : (φ a).val = g := congrArg Subtype.val ha
  change coordinateProjection (componentWords c A label) (L (f (ρ g x))) =
    wordRep n d g (coordinateProjection (componentWords c A label) (L (f x)))
  rw [he,he,← hval]
  exact LinearMap.congr_fun ((T.comp f).isIntertwining' a) x

end Saxl.Balance
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Saxl.Balance.balance_support_of_surjective_oai.{u_1, u_2, u_3} := @OAI.Saxl.Balance.balance_support_of_surjective_oai.{u_1, u_2, u_3}
