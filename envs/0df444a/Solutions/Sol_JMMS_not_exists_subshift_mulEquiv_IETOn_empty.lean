-- Prove2me | solution 1 for JMMS.not_exists_subshift_mulEquiv_IETOn_empty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:00:37.077425+00:00
-- url     : https://prove2.me/submissions/110ebad6-36ab-4518-8b3c-4eebd1b1d1a9

import Mathlib
import Definitions.Def_CantorSystems

section

open CantorSystems IntervalExchange
open Filter Topology
open scoped Pointwise

namespace JMMS
namespace IETPF511

/-! ## `IETOn Λ ∅` is commutative -/

lemma eventually_eq_of_finite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {f : α → β} {s : Set α} {a : α} {S : Set β} (hS : S.Finite) (hf : ∀ t, f t ∈ S)
    (hc : ContinuousWithinAt f s a) : ∀ᶠ t in 𝓝[s] a, f t = f a := by
  have hopen : IsOpen (S \ {f a})ᶜ := ((hS.subset Set.sdiff_subset).isClosed).isOpen_compl
  have hmem : f a ∈ (S \ {f a})ᶜ := by simp
  filter_upwards [hc (hopen.mem_nhds hmem)] with t ht
  by_contra hne
  exact ht ⟨hf t, hne⟩

lemma eventually_of_continuousAt {g : UnitAddCircle → UnitAddCircle} (ha : (angles g).Finite)
    {x : UnitAddCircle} (hc : ContinuousAt g x) : ∀ᶠ z in 𝓝 x, g z - z = g x - x := by
  have := eventually_eq_of_finite (s := Set.univ) ha (fun t => ⟨t, rfl⟩)
    ((hc.sub continuousAt_id).continuousWithinAt)
  simpa [nhdsWithin_univ] using this

/-- The interval exchange transformations form a subgroup (copied from `Solutions/IET/MemIET`):
only the inclusion `IET ≤ {g | (angles g).Finite}` is needed here. -/
def finAngles : Subgroup (Equiv.Perm UnitAddCircle) where
  carrier := {g | (angles g).Finite}
  one_mem' := by
    refine (Set.finite_singleton (0 : UnitAddCircle)).subset ?_
    rintro _ ⟨x, rfl⟩
    simp
  mul_mem' := by
    rintro g h hga hha
    refine (Set.Finite.image2 (· + ·) hga hha).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨_, ⟨h x, rfl⟩, _, ⟨x, rfl⟩, by simp [Equiv.Perm.mul_apply]⟩
  inv_mem' := by
    rintro g hga
    refine (hga.image Neg.neg).subset ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨_, ⟨g⁻¹ y, rfl⟩, by simp⟩

lemma angles_finite_of_mem_IET {g : Equiv.Perm UnitAddCircle} (hg : g ∈ IET) :
    (angles g).Finite := by
  have : IET ≤ finAngles := by
    unfold IET
    rw [Subgroup.closure_le]
    intro g hg
    exact hg.2.1
  exact this hg

lemma exists_rotation (Λ : AddSubgroup UnitAddCircle) (g : IETOn Λ ∅) :
    ∃ c : UnitAddCircle, ∀ z, (g : Equiv.Perm UnitAddCircle) z = z + c := by
  obtain ⟨⟨hIET, -⟩, hc⟩ := g.2
  have ha := angles_finite_of_mem_IET hIET
  have hlc : IsLocallyConstant
      (fun z => (g : Equiv.Perm UnitAddCircle) z - z) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    exact eventually_of_continuousAt ha (hc x (by simp [cosetsOf])).1
  refine ⟨(g : Equiv.Perm UnitAddCircle) 0 - 0, fun z => ?_⟩
  have := hlc.apply_eq_of_preconnectedSpace z 0
  rw [← this]
  abel

lemma IETOn_empty_comm (Λ : AddSubgroup UnitAddCircle) (g h : IETOn Λ ∅) : g * h = h * g := by
  obtain ⟨c, hc⟩ := exists_rotation Λ g
  obtain ⟨d, hd⟩ := exists_rotation Λ h
  apply Subtype.ext
  apply Equiv.ext
  intro z
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hc, hd]
  abel

/-! ## Swaps in the topological full group -/

section Swap

variable {Γ X : Type*} [AddGroup Γ] [AddAction Γ X] [TopologicalSpace X]

/-- The involution exchanging `U` and `α +ᵥ U` by `α`, identity elsewhere. -/
noncomputable def swapFun (U : Set X) (α : Γ) (y : X) : X := by
  classical
  exact if y ∈ U then α +ᵥ y else if y ∈ α +ᵥ U then -α +ᵥ y else y

omit [TopologicalSpace X] in
lemma swapFun_involutive {U : Set X} {α : Γ} (hd : Disjoint U (α +ᵥ U)) :
    Function.Involutive (swapFun U α) := by
  classical
  intro y
  by_cases hy : y ∈ U
  · have h1 : α +ᵥ y ∈ α +ᵥ U := Set.vadd_mem_vadd_set hy
    have h2 : α +ᵥ y ∉ U := fun h => Set.disjoint_left.1 hd h h1
    simp [swapFun, hy, h1, h2]
  · by_cases hy' : y ∈ α +ᵥ U
    · have h1 : -α +ᵥ y ∈ U := by
        obtain ⟨u, hu, rfl⟩ := hy'
        simpa using hu
      simp [swapFun, hy, hy', h1]
    · simp [swapFun, hy, hy']

/-- The local form of `swapFun`: near every point it agrees with a group element. -/
lemma swapFun_local (hcont : ∀ γ : Γ, Continuous (fun y : X => γ +ᵥ y)) {U : Set X} {α : Γ}
    (hU : IsClopen U) (x : X) :
    ∃ V ∈ 𝓝 x, ∃ γ : Γ, ∀ y ∈ V, swapFun U α y = γ +ᵥ y := by
  classical
  have hαU : IsClopen (α +ᵥ U) := by
    have : (α +ᵥ U) = (fun y => -α +ᵥ y) ⁻¹' U := by
      ext y
      simp [Set.mem_vadd_set_iff_neg_vadd_mem]
    rw [this]
    exact hU.preimage (hcont _)
  by_cases hx : x ∈ U
  · exact ⟨U, hU.isOpen.mem_nhds hx, α, fun y hy => by simp [swapFun, hy]⟩
  · by_cases hx' : x ∈ α +ᵥ U
    · refine ⟨Uᶜ ∩ (α +ᵥ U), Filter.inter_mem (hU.compl.isOpen.mem_nhds hx)
        (hαU.isOpen.mem_nhds hx'), -α, fun y hy => ?_⟩
      have : y ∉ U := hy.1
      simp [swapFun, this, hy.2]
    · refine ⟨Uᶜ ∩ (α +ᵥ U)ᶜ, Filter.inter_mem (hU.compl.isOpen.mem_nhds hx)
        (hαU.compl.isOpen.mem_nhds hx'), 0, fun y hy => ?_⟩
      have h1 : y ∉ U := hy.1
      have h2 : y ∉ α +ᵥ U := hy.2
      simp [swapFun, h1, h2]

lemma swapFun_continuous (hcont : ∀ γ : Γ, Continuous (fun y : X => γ +ᵥ y)) {U : Set X} {α : Γ}
    (hU : IsClopen U) : Continuous (swapFun U α) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨V, hV, γ, hγ⟩ := swapFun_local hcont (α := α) hU x
  exact (hcont γ).continuousAt.congr (Filter.mem_of_superset hV fun y hy => (hγ y hy).symm)

/-- The swap as a homeomorphism. -/
noncomputable def swapHomeo (hcont : ∀ γ : Γ, Continuous (fun y : X => γ +ᵥ y)) {U : Set X}
    {α : Γ} (hU : IsClopen U) (hd : Disjoint U (α +ᵥ U)) : X ≃ₜ X where
  toEquiv := (swapFun_involutive hd).toPerm _
  continuous_toFun := swapFun_continuous hcont hU
  continuous_invFun := swapFun_continuous hcont hU

lemma swapHomeo_apply (hcont : ∀ γ : Γ, Continuous (fun y : X => γ +ᵥ y)) {U : Set X}
    {α : Γ} (hU : IsClopen U) (hd : Disjoint U (α +ᵥ U)) (y : X) :
    swapHomeo hcont hU hd y = swapFun U α y := rfl

lemma swapHomeo_mem (hcont : ∀ γ : Γ, Continuous (fun y : X => γ +ᵥ y)) {U : Set X}
    {α : Γ} (hU : IsClopen U) (hd : Disjoint U (α +ᵥ U)) :
    swapHomeo hcont hU hd ∈ topologicalFullGroup Γ X := by
  intro x
  obtain ⟨V, hV, γ, hγ⟩ := swapFun_local hcont (α := α) hU x
  exact ⟨V, hV, γ, fun y hy => by rw [swapHomeo_apply]; exact hγ y hy⟩

end Swap

/-! ## The topological full group of a Cantor minimal system is not commutative -/

section NonComm

variable {Γ X : Type*} [AddGroup Γ] [AddAction Γ X] [TopologicalSpace X]

lemma orbit_infinite [T1Space X] (hmin : AddAction.IsMinimal Γ X)
    (hiso : ∀ x : X, ¬ IsOpen ({x} : Set X)) (x : X) : (AddAction.orbit Γ x).Infinite := by
  intro hfin
  have hcl : IsClosed (AddAction.orbit Γ x) := hfin.isClosed
  have huniv : AddAction.orbit Γ x = Set.univ := by
    have := (hmin.dense_orbit x).closure_eq
    rwa [hcl.closure_eq] at this
  have : Finite X := by
    rw [← Set.finite_univ_iff, ← huniv]
    exact hfin
  exact hiso x (isOpen_discrete _)

lemma exists_three [T1Space X] (hmin : AddAction.IsMinimal Γ X)
    (hiso : ∀ x : X, ¬ IsOpen ({x} : Set X)) (x : X) :
    ∃ α β : Γ, α +ᵥ x ≠ x ∧ β +ᵥ x ≠ x ∧ α +ᵥ x ≠ β +ᵥ x := by
  have hinf := orbit_infinite hmin hiso x
  obtain ⟨y, hy, hyx⟩ := (hinf.sdiff (Set.finite_singleton x)).nonempty
  obtain ⟨α, rfl⟩ := hy
  obtain ⟨z, hz, hzx⟩ := (hinf.sdiff (Set.toFinite ({x, α +ᵥ x} : Set X))).nonempty
  obtain ⟨β, rfl⟩ := hz
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, not_or] at hyx hzx
  exact ⟨α, β, hyx, hzx.1, fun h => hzx.2 h.symm⟩

lemma exists_clopen [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    (hcont : ∀ γ : Γ, Continuous (fun y : X => γ +ᵥ y)) (x : X) (α β : Γ)
    (h1 : α +ᵥ x ≠ x) (h2 : β +ᵥ x ≠ x) (h3 : α +ᵥ x ≠ β +ᵥ x) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ Disjoint U (α +ᵥ U) ∧ Disjoint U (β +ᵥ U) ∧
      Disjoint (α +ᵥ U) (β +ᵥ U) := by
  obtain ⟨A0, A1, hA0, hA1, hxA0, hxA1, hA⟩ := t2_separation h1.symm
  obtain ⟨B0, B2, hB0, hB2, hxB0, hxB2, hB⟩ := t2_separation h2.symm
  obtain ⟨C1, C2, hC1, hC2, hxC1, hxC2, hC⟩ := t2_separation h3
  set W : Set X := A0 ∩ B0 ∩ (fun y => α +ᵥ y) ⁻¹' (A1 ∩ C1) ∩ (fun y => β +ᵥ y) ⁻¹' (B2 ∩ C2)
  have hW : W ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ ⟨⟨⟨hxA0, hxB0⟩, hxA1, hxC1⟩, hxB2, hxC2⟩
    exact ((hA0.inter hB0).inter ((hA1.inter hC1).preimage (hcont α))).inter
      ((hB2.inter hC2).preimage (hcont β))
  obtain ⟨U, ⟨hxU, hUc⟩, hUW⟩ := (nhds_basis_clopen x).mem_iff.1 hW
  have hαU : α +ᵥ U ⊆ A1 ∩ C1 := by
    rintro _ ⟨u, hu, rfl⟩; exact (hUW hu).1.2
  have hβU : β +ᵥ U ⊆ B2 ∩ C2 := by
    rintro _ ⟨u, hu, rfl⟩; exact (hUW hu).2
  have hU0 : U ⊆ A0 ∩ B0 := fun u hu => (hUW hu).1.1
  refine ⟨U, hUc, hxU, ?_, ?_, ?_⟩
  · exact hA.mono (fun u hu => (hU0 hu).1) (fun u hu => (hαU hu).1)
  · exact hB.mono (fun u hu => (hU0 hu).2) (fun u hu => (hβU hu).1)
  · exact hC.mono (fun u hu => (hαU hu).2) (fun u hu => (hβU hu).2)

lemma not_comm [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    (hcont : ∀ γ : Γ, Continuous (fun y : X => γ +ᵥ y)) (hmin : AddAction.IsMinimal Γ X)
    (hiso : ∀ x : X, ¬ IsOpen ({x} : Set X)) (x : X) :
    ∃ a b : topologicalFullGroup Γ X, a * b ≠ b * a := by
  classical
  obtain ⟨α, β, h1, h2, h3⟩ := exists_three hmin hiso x
  obtain ⟨U, hU, hxU, hdα, hdβ, hdαβ⟩ := exists_clopen hcont x α β h1 h2 h3
  refine ⟨⟨swapHomeo hcont hU hdα, swapHomeo_mem hcont hU hdα⟩,
    ⟨swapHomeo hcont hU hdβ, swapHomeo_mem hcont hU hdβ⟩, fun h => ?_⟩
  have hx := congrArg (fun g : topologicalFullGroup Γ X => (g : X ≃ₜ X) x) h
  simp only [Subgroup.coe_mul, Homeomorph.mul_apply, swapHomeo_apply] at hx
  have hαx : α +ᵥ x ∈ α +ᵥ U := Set.vadd_mem_vadd_set hxU
  have hβx : β +ᵥ x ∈ β +ᵥ U := Set.vadd_mem_vadd_set hxU
  have e1 : α +ᵥ x ∉ U := fun h => Set.disjoint_left.1 hdα h hαx
  have e2 : β +ᵥ x ∉ U := fun h => Set.disjoint_left.1 hdβ h hβx
  have e3 : α +ᵥ x ∉ β +ᵥ U := fun h => Set.disjoint_left.1 hdαβ hαx h
  have e4 : β +ᵥ x ∉ α +ᵥ U := fun h => Set.disjoint_left.1 hdαβ h hβx
  simp [swapFun, hxU, e1, e2, e3, e4] at hx
  exact h3 hx.symm

end NonComm

lemma subshift_vadd_continuous {Λ : Type*} [AddGroup Λ] {k : ℕ} (S : Subshift Λ (Fin k))
    (γ : Λ) : Continuous (fun y : S => γ +ᵥ y) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun δ => (continuous_apply (δ + γ)).comp continuous_subtype_val

end IETPF511

theorem chk_not_exists_subshift_mulEquiv_IETOn_empty
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG) :
    ¬ ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      Nonempty (topologicalFullGroup Λ S ≃* IETOn Λ ∅) := by
  rintro ⟨k, S, ⟨⟨x⟩, hcpt, -, htd, hiso⟩, hmin, ⟨e⟩⟩
  have := hcpt
  have := htd
  obtain ⟨a, b, hab⟩ := IETPF511.not_comm (IETPF511.subshift_vadd_continuous S) hmin hiso x
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact IETPF511.IETOn_empty_comm Λ _ _

end JMMS

end

open CantorSystems IntervalExchange
theorem solution
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG) :
    ¬ ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      Nonempty (topologicalFullGroup Λ S ≃* IETOn Λ ∅) :=
  JMMS.chk_not_exists_subshift_mulEquiv_IETOn_empty Λ hΛ hfg
