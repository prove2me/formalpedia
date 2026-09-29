-- Prove2me | solution 1 for HeckeCohomology.exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a8fd35bc-6657-5907-9a3f-ccfb024a55e2

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke
import Theorems.Thm_CohCarrier_subsingleton_H2_GammaH
import Theorems.Thm_HeckeCohomology_heckeH1_natural
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH

set_option autoImplicit false

namespace D2

open groupCohomology CategoryTheory

section LinAlg

variable {F : Type*} [Field F]

theorem coe_restrict_pow {M : Type*} [AddCommGroup M] [Module F M] (f : M →ₗ[F] M)
    (P : Submodule F M) (h : ∀ v ∈ P, f v ∈ P) (k : ℕ) (v : ↥P) :
    (((f.restrict h) ^ k) v : M) = (f ^ k) (v : M) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

theorem exists_common_ker_of_nilpotent : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → (∀ i, IsNilpotent (T i)) → Nontrivial M →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT hnil hM hd
  by_cases hz : ∀ i, T i = 0
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact ⟨v, hv, fun i => by rw [hz i, LinearMap.zero_apply]⟩
  push_neg at hz
  obtain ⟨i₀, hi₀⟩ := hz
  set P : Submodule F M := LinearMap.ker (T i₀) with hP
  have hPtop : P ≠ ⊤ := fun h => hi₀ (LinearMap.ker_eq_top.mp h)
  have hPbot : P ≠ ⊥ := by
    intro h
    have hinj : Function.Injective (T i₀) := LinearMap.ker_eq_bot.mp h
    obtain ⟨k, hk⟩ := hnil i₀
    have hinjk : Function.Injective ((T i₀) ^ k) := by
      rw [Module.End.coe_pow]; exact Function.Injective.iterate hinj k
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact hv (hinjk (by rw [hk, map_zero, LinearMap.zero_apply]))
  have hstab : ∀ i, ∀ v ∈ P, T i v ∈ P := by
    intro i v hv
    rw [hP, LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, (hT i₀ i).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P →ₗ[F] ↥P := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hnil' : ∀ i, IsNilpotent (T' i) := by
    intro i
    obtain ⟨k, hk⟩ := hnil i
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    change ((((T i).restrict (hstab i)) ^ k) v : M) = ((0 : ↥P →ₗ[F] ↥P) v : M)
    rw [coe_restrict_pow, hk]
    rfl
  haveI : Nontrivial ↥P := Submodule.nontrivial_iff_ne_bot.mpr hPbot
  have hlt : Module.finrank F ↥P < d := hd ▸ Submodule.finrank_lt hPtop
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' hnil' inferInstance rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

theorem exists_common_ker_of_range_le : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → ∀ (P : Submodule F M), P ≠ ⊤ → (∀ i x, T i x ∈ P) →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT P hP hTP hd
  by_cases hall : ∀ i, IsNilpotent (T i)
  ·
    have hex : ∃ v : M, v ∉ P := by
      by_contra h
      push_neg at h
      exact hP (Submodule.eq_top_iff'.mpr h)
    obtain ⟨v, hv⟩ := hex
    have hv0 : v ≠ 0 := fun h => hv (h ▸ P.zero_mem)
    haveI : Nontrivial M := nontrivial_of_ne v 0 hv0
    exact exists_common_ker_of_nilpotent d T hT hall inferInstance hd
  push_neg at hall
  obtain ⟨i₀, hi₀⟩ := hall
  set f := T i₀ with hf

  obtain ⟨k, hk, hk1⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow f).and (Filter.eventually_ge_atTop 1)).exists
  set P' : Submodule F M := LinearMap.ker (f ^ k) with hP'
  set Q : Submodule F M := LinearMap.range (f ^ k) with hQ
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hi₀
    exact ⟨k, LinearMap.range_eq_bot.mp h⟩
  have hP'top : P' ≠ ⊤ := by
    intro h
    have hdis := hk.disjoint
    rw [h] at hdis
    exact hQbot (top_disjoint.mp hdis)

  have hQP : Q ≤ P := by
    rintro _ ⟨x, rfl⟩
    have hfk : f ^ k = f * f ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk1]
    rw [hfk, Module.End.mul_apply]
    exact hTP i₀ _

  have hP'P : P.comap P'.subtype ≠ ⊤ := by
    intro h
    have hle : P' ≤ P := fun v hv => by
      have : (⟨v, hv⟩ : ↥P') ∈ P.comap P'.subtype := by rw [h]; trivial
      exact this
    apply hP
    rw [eq_top_iff, ← hk.codisjoint.eq_top]
    exact sup_le hle hQP

  have hstab : ∀ i, ∀ v ∈ P', T i v ∈ P' := by
    intro i v hv
    rw [hP', LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, ((hT i₀ i).pow_left k).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P' →ₗ[F] ↥P' := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hTP' : ∀ i (x : ↥P'), T' i x ∈ P.comap P'.subtype := fun i x => hTP i (x : M)
  have hlt : Module.finrank F ↥P' < d := hd ▸ Submodule.finrank_lt hP'top
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' (P.comap P'.subtype) hP'P hTP' rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

theorem exists_common_eigenvector {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    {ι : Type*} (T : ι → M →ₗ[F] M) (hT : ∀ i j, Commute (T i) (T j)) (c : ι → F)
    (P : Submodule F M) (hP : P ≠ ⊤) (hTP : ∀ i x, T i x - c i • x ∈ P) :
    ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = c i • v := by
  let T' : ι → M →ₗ[F] M := fun i => T i - c i • 1
  have hT' : ∀ i j, Commute (T' i) (T' j) := by
    intro i j
    refine Commute.sub_left (Commute.sub_right (hT i j) ?_) (Commute.sub_right ?_ ?_)
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.refl (1 : M →ₗ[F] M)).smul_right _).smul_left _
  have hTP' : ∀ i x, T' i x ∈ P := fun i x => by
    simpa [T', LinearMap.sub_apply, LinearMap.smul_apply] using hTP i x
  obtain ⟨v, hv, hTv⟩ := exists_common_ker_of_range_le _ T' hT' P hP hTP' rfl
  refine ⟨v, hv, fun i => ?_⟩
  have := hTv i
  simp only [T', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

end LinAlg

section Fin

open scoped MatrixGroups

theorem fg_SL2Z : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

theorem gamma1_le_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    CongruenceSubgroup.Gamma1 N ≤ CohCarrier.GammaH N H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨by rw [CongruenceSubgroup.Gamma0_mem]; exact hA.2.2, ?_⟩
  have h1 : CohCarrier.gamma0Units N ⟨A, by rw [CongruenceSubgroup.Gamma0_mem]; exact hA.2.2⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units]
    exact hA.2.1
  rw [h1]
  exact one_mem H

scoped instance fg_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) : Group.FG ↥(CohCarrier.GammaH N H) := by
  haveI := fg_SL2Z
  haveI : (CohCarrier.GammaH N H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (gamma1_le_gammaH N H)
  exact Subgroup.fg_of_index_ne_zero _

theorem cocycle_eq_zero_of_closure {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (f : cocycles₁ A) (hf : ∀ s ∈ S, f s = 0) : f = 0 := by
  have key : ∀ g : G, f g = 0 := by
    intro g
    have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hf x hx
    | one => exact cocycles₁_map_one f
    | mul x y _ _ hx hy => rw [(mem_cocycles₁_iff f).mp f.2 x y, hx, hy, map_zero, add_zero]
    | inv x _ hx =>
      have h := (mem_cocycles₁_iff f).mp f.2 x x⁻¹
      rw [mul_inv_cancel, cocycles₁_map_one, hx, add_zero] at h
      have h2 : (A.ρ x⁻¹) ((A.ρ x) (f x⁻¹)) = f x⁻¹ := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [← h2, ← h, map_zero]
  exact Subtype.ext (funext key)

scoped instance finite_H1 {k G : Type} [Field k] [Group G] [hG : Group.FG G] (A : Rep k G) [Module.Finite k A] :
    Module.Finite k (H1 A) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp hG
  haveI : Finite S := hSfin.to_subtype

  let ev : ↥(cocycles₁ A) →ₗ[k] (S → A) :=
    { toFun := fun f s => f (s : G)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro f g h
    have : f - g = 0 := cocycle_eq_zero_of_closure A S hS (f - g) (fun s hs => by
      have := congrFun h ⟨s, hs⟩
      change f s = g s at this
      change (f : G → A) s - (g : G → A) s = 0
      exact sub_eq_zero.mpr this)
    exact sub_eq_zero.mp this
  haveI : Module.Finite k ↥(cocycles₁ A) := Module.Finite.of_injective ev hev
  exact Module.Finite.of_surjective (H1π A).hom (by exact HeckeCohomology.H1π_surjective A)

end Fin

end D2
p2m_reactivate "P2MW.S_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH.D2"

open D2 groupCohomology CategoryTheory in
theorem solution
    (N r : ℕ) [NeZero N] (hrN : r ∣ N) (hr : 4 ≤ r) (H : Subgroup (ZMod N)ˣ)
    (hH : ∀ u ∈ H, ZMod.castHom hrN (ZMod r) (u : ZMod N) = 1)
    {κ : Type} [Field κ]
    {X : CategoryTheory.ShortComplex (Rep κ ↥(CohCarrier.GammaH N H))} (hX : X.ShortExact)
    [Module.Finite κ X.X₂]
    {ι : Type} (S₁ S₂ : ι → Subgroup ↥(CohCarrier.GammaH N H)) (c : ∀ i, ↥(S₂ i) →* ↥(S₁ i))
    [∀ i, (S₂ i).FiniteIndex]
    (φ₂ : ∀ i, X.X₂ →ₗ[κ] X.X₂) (hφ₂ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i))
    (φ₃ : ∀ i, X.X₃ →ₗ[κ] X.X₃) (hφ₃ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i))
    (hg : ∀ (i : ι) (b : X.X₂), X.g.hom (φ₂ i b) = φ₃ i (X.g.hom b))
    (hcomm : ∀ i j : ι,
      Commute (HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i))
        (HeckeCohomology.heckeH1 (S₁ j) (S₂ j) (c j) X.X₂ (φ₂ j) (hφ₂ j)))
    (lam : ι → κ)
    (hocc : ∃ y : groupCohomology.H1 X.X₃, y ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i) (hφ₃ i) y = lam i • y) :
    ∃ x : groupCohomology.H1 X.X₂, x ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i) x = lam i • x := by
  classical
  obtain ⟨y, hy0, hy⟩ := hocc

  let g1 : H1 X.X₂ →ₗ[κ] H1 X.X₃ := (map (MonoidHom.id _) X.g 1).hom
  haveI : Subsingleton (groupCohomology X.X₁ 2) := CohCarrier.subsingleton_H2_GammaH N r hrN hr H hH X.X₁
  have hsurj : Function.Surjective g1 := by
    intro z
    have hex := (mapShortComplex₃_exact hX (rfl : 1 + 1 = 2)).moduleCat_range_eq_ker
    have hz0 : (mapShortComplex₃ hX (rfl : 1 + 1 = 2)).g.hom z = 0 :=
      @Subsingleton.elim (groupCohomology X.X₁ 2) _ _ _
    have hz := LinearMap.mem_ker.mpr hz0
    rw [← hex] at hz
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, hw⟩

  let T₂ : ι → H1 X.X₂ →ₗ[κ] H1 X.X₂ := fun i => HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i)
  let T₃ : ι → H1 X.X₃ →ₗ[κ] H1 X.X₃ := fun i => HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i) (hφ₃ i)
  have hequiv : ∀ (i : ι) (x : H1 X.X₂), g1 (T₂ i x) = T₃ i (g1 x) := fun i x =>
    (HeckeCohomology.heckeH1_natural (S₁ i) (S₂ i) (c i) X.g (φ₂ i) (hφ₂ i) (φ₃ i) (hφ₃ i) (hg i) x).symm

  let L : Submodule κ (H1 X.X₃) := κ ∙ y
  let W : Submodule κ (H1 X.X₂) := L.comap g1
  have hWstab : ∀ i, ∀ w ∈ W, T₂ i w ∈ W := by
    intro i w hw
    change g1 (T₂ i w) ∈ L
    rw [hequiv]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
    change g1 w ∈ L at hw
    rw [← ha, map_smul, hy i, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
  let TW : ι → ↥W →ₗ[κ] ↥W := fun i => (T₂ i).restrict (hWstab i)
  have hTW : ∀ i j, Commute (TW i) (TW j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hcomm i j).eq (v : H1 X.X₂))
  let P : Submodule κ ↥W := (LinearMap.ker g1).comap W.subtype
  have hP : P ≠ ⊤ := by
    obtain ⟨w, hw⟩ := hsurj y
    have hwW : w ∈ W := by change g1 w ∈ L; rw [hw]; exact Submodule.mem_span_singleton_self y
    intro htop
    have : (⟨w, hwW⟩ : ↥W) ∈ P := by rw [htop]; exact Submodule.mem_top
    change w ∈ LinearMap.ker g1 at this
    rw [LinearMap.mem_ker, hw] at this
    exact hy0 this
  have hTP : ∀ i (x : ↥W), TW i x - lam i • x ∈ P := by
    intro i x
    change ((T₂ i x : H1 X.X₂) - lam i • (x : H1 X.X₂)) ∈ LinearMap.ker g1
    rw [LinearMap.mem_ker, map_sub, map_smul, hequiv]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (show g1 (x : H1 X.X₂) ∈ L from x.2)
    rw [← ha, map_smul, hy i, smul_smul, smul_smul, mul_comm, sub_self]
  haveI : Module.Finite κ (H1 X.X₂) := D2.finite_H1 X.X₂
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector TW hTW lam P hP hTP
  refine ⟨(v : H1 X.X₂), fun h => hv0 (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hv i)

end S_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH
end P2MW
export P2MW.S_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH (solution)
