-- Prove2me | solution 1 for HopfAlgebra.wittHom_coeff_mem_map_adjoin_of_surjective_of_wittHomShift_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/df3ddd54-8721-534b-b0c7-d6cdf2301fe8

import Mathlib
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField
import Theorems.Thm_Bialgebra_exists_surjective_bialgHom_ker_eq_map_ker
import Theorems.Thm_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker
import Theorems.Thm_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer
import Theorems.Thm_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_wittHom_coeff_mem_map_adjoin_of_surjective_of_wittHomShift_surjective
p2m_attr_erase "instance" "CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of"
p2m_attr_erase "simp" "Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl"

set_option autoImplicit false

universe u v w

theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [NeZero n]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (B : Type w) [CommRing B] [Bialgebra k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π)
    (hsat : Function.Surjective (Deformation.wittHomShift k p n A)) :
    ∀ (y : Deformation.wittHom k p n B) (i : Fin n),
      (y : TruncatedWittVector p n B).coeff i ∈
        (Algebra.adjoin k {a : A | ∃ x : Deformation.wittHom k p n A, ∃ j : Fin n,
          (x : TruncatedWittVector p n A).coeff j = a}).map (π : A →ₐ[k] B)  := by
  classical
  intro y i
  obtain ⟨Aw, _, _, _, _, Au, _, _, _, _, μ, ι, hμ, hι, hker, hunip, horth⟩ :=
    HopfAlgebra.exists_wittOrthogonal_unipotent_splitting_of_perfectField.{u, v, w} k p A
  obtain ⟨D, _, _, ρ, hρ, hkerρ⟩ :=
    Bialgebra.exists_surjective_bialgHom_ker_eq_map_ker k π μ hπ hμ

  have hy0 : Deformation.wittHomMap p n ρ y = 0 := by
    refine horth D (ρ.comp π) (hρ.comp hπ) ?_ n _
    intro a ha
    have hmem : (π : A →ₐ[k] B) a ∈ Ideal.map (π : A →ₐ[k] B) (RingHom.ker (μ : A →ₐ[k] Aw)) :=
      Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker]; exact ha)
    rw [← hkerρ, RingHom.mem_ker] at hmem
    exact hmem

  have hcoef : ∀ j, (y : TruncatedWittVector p n B).coeff j ∈ HopfAlgebra.hopfKer ρ :=
    (Deformation.wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer ρ y).mp hy0

  have hiso := HopfAlgebra.map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker k π μ ρ hπ hμ hρ hkerρ

  have hAu := Deformation.adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual k p Au hunip
  have hsub₁ : (HopfAlgebra.hopfKer μ : Set A) ⊆
      Algebra.adjoin k {a : A | ∃ (m : ℕ) (x : Deformation.wittHom k p m A) (j : Fin m),
        (x : TruncatedWittVector p m A).coeff j = a} := by
    intro a ha
    obtain ⟨b, rfl⟩ := (hker a).mp ha

    have hb : b ∈ Algebra.adjoin k {b : Au | ∃ (m : ℕ) (x : Deformation.wittHom k p m Au) (j : Fin m),
        (x : TruncatedWittVector p m Au).coeff j = b} := by rw [hAu]; exact Algebra.mem_top
    have hmap : (ι : Au →ₐ[k] A) b ∈ (Algebra.adjoin k {b : Au | ∃ (m : ℕ) (x : Deformation.wittHom k p m Au)
        (j : Fin m), (x : TruncatedWittVector p m Au).coeff j = b}).map (ι : Au →ₐ[k] A) :=
      Subalgebra.mem_map.mpr ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at hmap
    refine Algebra.adjoin_mono ?_ hmap
    rintro _ ⟨b', ⟨m, x, j, rfl⟩, rfl⟩
    exact ⟨m, Deformation.wittHomMap p m ι x, j, Deformation.coeff_wittHomMap ι x j⟩

  have hsub₂ : Algebra.adjoin k {a : A | ∃ (m : ℕ) (x : Deformation.wittHom k p m A) (j : Fin m),
        (x : TruncatedWittVector p m A).coeff j = a} ≤
      Algebra.adjoin k {a : A | ∃ x : Deformation.wittHom k p n A, ∃ j : Fin n,
        (x : TruncatedWittVector p n A).coeff j = a} := by

    set T : Subalgebra k A := Algebra.adjoin k {a : A | ∃ x : Deformation.wittHom k p n A, ∃ j : Fin n,
        (x : TruncatedWittVector p n A).coeff j = a} with hT
    let P : ℕ → Prop := fun m => ∀ (x : Deformation.wittHom k p m A) (j : Fin m),
      (x : TruncatedWittVector p m A).coeff j ∈ T
    have hPn : P n := fun x j => Algebra.subset_adjoin ⟨x, j, rfl⟩

    have hshift : ∀ m, P (m + 1) → P m := by
      intro m hP x j
      have h := hP (Deformation.wittHomShift k p m A x) j.succ
      rwa [Deformation.coe_wittHomShift, Deformation.TruncWitt.coeff_shift_succ] at h

    have hsat' : ∀ r, Function.Surjective (Deformation.wittHomShift k p (n + r) A) := by
      intro r
      induction r with
      | zero => exact hsat
      | succ r ih =>
        intro y

        obtain ⟨z, hz⟩ := ih (Deformation.wittHomRestrict k p A (Nat.le_succ (n + r + 1)) y)
        have hy0 : (y : TruncatedWittVector p (n + r + 1 + 1) A).coeff 0 = 0 := by
          have h1 : ((Deformation.wittHomRestrict k p A (Nat.le_succ (n + r + 1)) y :
              Deformation.wittHom k p (n + r + 1) A) : TruncatedWittVector p (n + r + 1) A).coeff 0 =
              (y : TruncatedWittVector p (n + r + 1 + 1) A).coeff 0 := by
            rw [Deformation.coe_wittHomRestrict, TruncatedWittVector.coeff_truncate]
            rfl
          rw [← h1, ← hz, Deformation.coe_wittHomShift]
          exact Deformation.TruncWitt.coeff_shift_zero _

        let y' : TruncatedWittVector p (n + r + 1) A :=
          TruncatedWittVector.mk p fun i => (y : TruncatedWittVector p (n + r + 1 + 1) A).coeff i.succ
        have hyy' : Deformation.TruncWitt.shift y' = (y : TruncatedWittVector p (n + r + 1 + 1) A) := by
          refine TruncatedWittVector.ext fun i => ?_
          refine Fin.cases ?_ (fun i' => ?_) i
          · rw [Deformation.TruncWitt.coeff_shift_zero, hy0]
          · rw [Deformation.TruncWitt.coeff_shift_succ]
            rfl
        have hy'mem : y' ∈ Deformation.wittHom k p (n + r + 1) A := by
          have hy := y.2
          rw [Deformation.mem_wittHom_iff] at hy ⊢
          apply Deformation.TruncWitt.shift_injective
          rw [← Deformation.TruncWitt.map_shift, hyy', hy, map_add, ← Deformation.TruncWitt.map_shift,
            ← Deformation.TruncWitt.map_shift, hyy']
        exact ⟨⟨y', hy'mem⟩, Subtype.ext hyy'⟩

    have hup : ∀ r, P (n + r) := by
      intro r
      induction r with
      | zero => exact hPn
      | succ r ih =>
        intro x j
        obtain ⟨w, rfl⟩ := hsat' r x
        rw [Deformation.coe_wittHomShift]
        refine Fin.cases ?_ (fun j' => ?_) j
        · rw [Deformation.TruncWitt.coeff_shift_zero]; exact zero_mem T
        · rw [Deformation.TruncWitt.coeff_shift_succ]; exact ih w j'
    have hdown : ∀ d m, m + d = n → P m := by
      intro d
      induction d with
      | zero => intro m hm; rw [Nat.add_zero] at hm; subst hm; exact hPn
      | succ d ih => intro m hm; exact hshift m (ih (m + 1) (by omega))
    have hP : ∀ m, P m := by
      intro m
      by_cases hmn : m ≤ n
      · exact hdown (n - m) m (by omega)
      · have h := hup (m - n)
        rwa [show n + (m - n) = m by omega] at h

    refine Algebra.adjoin_le ?_
    rintro _ ⟨m, x, j, rfl⟩
    exact hP m x j

  have hmem : (y : TruncatedWittVector p n B).coeff i ∈ (HopfAlgebra.hopfKer μ).map (π : A →ₐ[k] B) := by
    rw [hiso]; exact hcoef i
  obtain ⟨a, ha, hai⟩ := Subalgebra.mem_map.mp hmem
  exact Subalgebra.mem_map.mpr ⟨a, hsub₂ (hsub₁ ha), hai⟩

end S_HopfAlgebra_wittHom_coeff_mem_map_adjoin_of_surjective_of_wittHomShift_surjective
end P2MW
export P2MW.S_HopfAlgebra_wittHom_coeff_mem_map_adjoin_of_surjective_of_wittHomShift_surjective (solution)
