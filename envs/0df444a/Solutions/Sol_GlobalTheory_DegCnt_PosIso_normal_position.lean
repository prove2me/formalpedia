-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.normal_position
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:08.925832+00:00
-- url     : https://prove2.me/submissions/27765869-16a3-4d7c-8efc-566965d7e76a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Dl_ne
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_e_mem_Ia
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_mono
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_le
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_X
import Theorems.Thm_P2M_GlobalTheory_DegCnt_PosIso_Ia_X__933463d23d40
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Xa_le_sup
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Xa_ist
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_step
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_II_le
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_hermForm_second_flag_X_z_eq_zero
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_exists_move_alt
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_exists_unitri
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_level_ind
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_smul_flag_vector_mem_reference_lattice
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_hermForm_ist_mem_coeffIdeal_of_mem_reference
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_exists_adapted
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_smul_add_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_isUnimod_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ N.F.Xa N.j ⊔ N.F'.Xa N.j, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ 2 • (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ≤ Λ' ∧ Λ' ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 ∧ 𝔠 • line 1 N.F.z ≤ Λ' := by
  intro K V _ _ _ _ _ _ _ _ H _ r N g Λ _ hT 𝔠 _ _ _ h𝔠
  have hΛ := hT.1
  have hγ : ∀ γ ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      (γ : K) * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K) :=
    fun γ h y hy => (h𝔠 N.j _ le_rfl (Dl_ne N) γ h y hy).1
  have hfg : Λ.FG := ((isUnimod_iff H Λ).1 hΛ.1).1.fg
  choose! v hv hvΛ using exists_adapted N Λ hfg
  obtain ⟨u, hu, huz, huv⟩ := exists_unitri N v hv
  have hz : (1 : K) ∈ lead N.F Λ (Fin.last r) := by rw [hΛ.2.1.2]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 hz
  have he' : l + ξ = (1 : K) • N.F.z := he
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N r hξ)
  obtain ⟨E, hE, hEz, hEX⟩ := exists_move_alt N (neg_mem hξ₂)
  have hvX : ∀ b : Fin r, N.j ≤ b.val → v b ∈ Ia N r := fun b hb => by
    simpa using add_mem (Ia_mono N b.isLt.le (hv b hb)) (e_mem_Ia N b hb b.isLt)
  have hsv : ∀ b : Fin r, N.j ≤ b.val → ∀ t : K, (u * E) (t • v b) = t • N.F.e b.castSucc := fun b hb t => by
    rw [map_smul, LinearEquiv.mul_apply, hEX _ (Ia_X N (hvX b hb)), huv b hb]
  have hmem : ∀ y, y ∈ (u * E) • Λ ↔ ∃ x ∈ Λ, (u * E) x = y := fun y =>
    Submodule.mem_smul_pointwise_iff_exists _ _ _
  have hG := mul_mem hu hE
  refine ⟨u * E, hG.1, fun y hy => (mem_fixingSubgroup_iff _).1 hG.2 y hy, ?_⟩
  rintro _ rfl
  refine ⟨?_, ?_, ?_⟩
  · refine Submodule.smul_le.2 fun γ hγ2 y hy => ?_
    have hγ1 : γ ∈ 𝔠 := Ideal.pow_le_self two_ne_zero hγ2
    refine level_ind N N.P0 (((u * E) • Λ).comap (γ • LinearMap.id)) (fun b => N.F.e b.castSucc)
      (fun b _ => by simp) (fun b hb y hy _ => ?_) r le_rfl y hy.1 (II_le N hy.2)
    have ht := hermForm_ist_mem_coeffIdeal_of_mem_reference N b hb hy
    refine ⟨smul_flag_vector_mem_reference_lattice N b ht, ?_⟩
    generalize H.B y (N.ist b) = t at ht
    rw [← hΛ.2.1.1] at ht
    obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 ht
    have he' : l + ξ = t • N.F.e b.castSucc := he
    obtain ⟨η₁, hη₁, η₂, hη₂, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N b.val hξ)
    have hI : t • N.F.e b.castSucc - η₂ ∈ Ia N (b.val + 1) :=
      sub_mem (Submodule.smul_mem _ _ (e_mem_Ia N b hb (Nat.lt_succ_self _))) (Ia_mono N (Nat.le_succ _) hη₂)
    have h1 := smul_add_mem N Λ hΛ γ (hγ γ hγ1) (fun w hw => X_iso N.F' (Ia_X' N hI) hw) hη₁
      (by convert hl using 1; rw [← he']; abel)
    rw [← algebraMap_smul K γ] at h1
    have h2 := hvΛ b hb _ h1 (Submodule.smul_mem _ _ hI)
    show γ • (t • N.F.e b.castSucc) ∈ (u * E) • Λ
    refine (hmem _).2 ⟨_, h2, ?_⟩
    rw [hsv b hb, ← algebraMap_smul K γ (t • _), smul_smul, map_smul, map_sub, map_smul, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, N.ist_e b b hb, Xa_ist N b hb _ (Ia_le N _ hη₂), if_pos rfl,
      smul_eq_mul, smul_eq_mul, mul_one, sub_zero]
  · rintro y ⟨hy, hyI⟩
    obtain ⟨x, hx, rfl⟩ := (hmem y).1 hy
    have hxI : x ∈ Ia N r := by
      have : Ia N r ≤ (Ia N r).map ((u * E : V ≃ₗ[K] V) : V →ₗ[K] V) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨v b, hvX b hb.1, by simpa using hsv b hb.1 1⟩
      obtain ⟨x', hx', e⟩ := this (II_le N hyI)
      rwa [← (u * E).injective e]
    refine level_ind N Λ (N.P0.comap (((u * E : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K))) v hv
      (fun b hb y hy hy' => ⟨hvΛ b hb y hy hy', ?_⟩) r le_rfl x hx hxI
    show (u * E) (_ • v b) ∈ N.P0
    rw [hsv b hb]
    refine smul_flag_vector_mem_reference_lattice N b ?_
    rw [← hΛ.2.1.1]
    show H.B y (N.ist b) • N.F.e b.castSucc ∈ Λ ⊔ rs (𝓞 K) (N.F.Xa b.val)
    have := sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right (S := Λ)
      (show _ ∈ rs (𝓞 K) (N.F.Xa b.val) from Ia_le N _ (Ia_step N b hb hy')))
    simpa using this
  · refine Submodule.smul_le.2 ?_
    rintro γ hγ1 _ ⟨t, ht, rfl⟩
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 ht
    have h1 := smul_add_mem N Λ hΛ γ (hγ γ hγ1) (y := N.F.z - ξ₂)
      (fun w hw => by
        rw [map_sub, LinearMap.sub_apply, B_swap0 H (hermForm_second_flag_X_z_eq_zero N hw), X_iso N.F' (Ia_X' N hξ₂) hw, sub_zero]) hξ₁
      (by convert hl using 1; rw [one_smul] at he'; rw [← he']; abel)
    show γ • (algebraMap (𝓞 K) K o • N.F.z) ∈ (u * E) • Λ
    rw [algebraMap_smul, smul_comm]
    refine Submodule.smul_mem _ _ ((hmem _).2 ⟨_, h1, ?_⟩)
    rw [← algebraMap_smul K γ, ← algebraMap_smul K γ N.F.z, map_smul, LinearEquiv.mul_apply, map_sub, hEz,
      hEX _ (Ia_X N hξ₂)]
    simp [huz]
end GlobalTheory.DegCnt.PosIso
