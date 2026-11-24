-- Prove2me | solution 1 for GlobalTheory.CotUniv.universal_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:42:58.280303+00:00
-- url     : https://prove2.me/submissions/f32334b8-8bb3-412b-af77-fe109ecc2ddc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
import Theorems.Thm_GlobalTheory_CotUniv_lhom_ext
import Theorems.Thm_GlobalTheory_CotUniv_sqProj_comp_sqIncl
import Theorems.Thm_GlobalTheory_CotUniv_sqKer_injective
import Theorems.Thm_GlobalTheory_CotUniv_sqKer_surjective
import Theorems.Thm_GlobalTheory_CotUniv_map_sqMap_tg
import Theorems.Thm_GlobalTheory_CotUniv_lie_nsmul
import Theorems.Thm_GlobalTheory_CotUniv_lieLift_mk
import Theorems.Thm_GlobalTheory_CotUniv_lieLift_basis
import Theorems.Thm_GlobalTheory_CotUniv_sum_lieBasis
import Theorems.Thm_GlobalTheory_CotUniv_lie_ext
import Theorems.Thm_GlobalTheory_CotUniv_snd_smul
import Theorems.Thm_GlobalTheory_CotUniv_snd_leibniz
import Theorems.Thm_GlobalTheory_CotUniv_exists_lift
import Theorems.Thm_GlobalTheory_CotUniv_sqMap_comp_sO
import Theorems.Thm_GlobalTheory_CotUniv_sqProj_comp_sqMap
import Theorems.Thm_GlobalTheory_CotUniv_tg_act
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_fst
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_snd



set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
namespace GlobalTheory.CotUniv
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ (S : LAlg R₀) (s : LHom Tw.O S) (π : LHom S Tw.O) (hπ : π.SqZero), π.comp s = LHom.id Tw.O →
    (∀ m : Fin g → π.ker, (∀ k, p • m k = 0) → ∃! φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s ∧ π.comp φ = (D.ptMap 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) ∧
    (∀ φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s → π.comp φ = (D.ptMap 0) → ∃! m : Fin g → π.ker, (∀ k, p • m k = 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k))) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∃ δ : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ LieDualModP p (Tw.O : Type) g,
    (∀ o f, δ ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • δ f) ∧ (∀ f f', δ (f * f') = (D.ptMap 0).1 f • δ f' + (D.ptMap 0).1 f' • δ f) ∧
    (∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (d : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ M),
      (∀ o f, d ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • d f) → (∀ f f', d (f * f') = (D.ptMap 0).1 f • d f' + (D.ptMap 0).1 f' • d f) →
      ∃! u : LieDualModP p (Tw.O : Type) g →ₗ[(Tw.O : Type)] M, ∀ f, d f = u (δ f)) ∧
    ∀ (a : Oe) (α : LHom (D.fin.AAx (D.ptIdx 0)) (D.fin.AAx (D.ptIdx 0))), α.comp (D.fin.sO (D.ptIdx 0)) = (D.fin.sO (D.ptIdx 0)) →
      B.map α (D.fin.y (D.ptIdx 0)) = (D.A.act a (D.fin.AAx (D.ptIdx 0)) (D.fin.sO (D.ptIdx 0)) ⟨(D.fin.y (D.ptIdx 0)), (mem_torP B p _).2 (D.fin.y_p _)⟩ : B.G (D.fin.AAx (D.ptIdx 0))) →
      ∀ f (l : Fin g → (Tw.O : Type)), δ f = Submodule.Quotient.mk l → δ (α.1 f) = Submodule.Quotient.mk ((D.H.ρL a)ᵀ *ᵥ l)) := by
  intro hyp R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  obtain ⟨hε, hy, huniq⟩ := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ 0) (D.pt_p 0)))
  change (D.ptMap 0).comp (D.fin.sO (D.ptIdx 0)) = _ at hε
  have huniq' : ∀ φ' : LHom (D.fin.AAx (D.ptIdx 0)) Tw.O,
      φ'.comp (D.fin.sO (D.ptIdx 0)) = LHom.id Tw.O → B.map φ' (D.fin.y (D.ptIdx 0)) = 0 →
        φ' = D.ptMap 0 := fun φ' h1 h2 =>
    eq_of_heq (huniq (D.ptIdx 0) φ' h1 (h2.trans (by simp [ptOf]))).2
  have H1 : ∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (m : Fin g → M),
      (∀ k, p • m k = 0) → ∃! φ : LHom (D.fin.AAx (D.ptIdx 0)) (sqAlg Tw.O M),
        φ.comp (D.fin.sO (D.ptIdx 0)) = sqIncl Tw.O M ∧ (sqProj Tw.O M).comp φ = D.ptMap 0 ∧
          B.map φ (D.fin.y (D.ptIdx 0)) = tgPt B Tw.O D.ch.gb m := fun M _ _ m hm =>
    (hyp D _ _ _ (sqProj_sqZero Tw.O M) (sqProj_comp_sqIncl Tw.O M)).1 (fun k => sqKer (m k))
      (fun k => by rw [← map_nsmul, hm, map_zero])
  have H2 : ∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M]
      (φ : LHom (D.fin.AAx (D.ptIdx 0)) (sqAlg Tw.O M)),
      φ.comp (D.fin.sO (D.ptIdx 0)) = sqIncl Tw.O M → (sqProj Tw.O M).comp φ = D.ptMap 0 →
      ∃! m : Fin g → M, (∀ k, p • m k = 0) ∧
        B.map φ (D.fin.y (D.ptIdx 0)) = tgPt B Tw.O D.ch.gb m := by
    intro M _ _ φ h1 h2
    obtain ⟨m, ⟨hm1, hm2⟩, hm3⟩ :=
      (hyp D _ _ _ (sqProj_sqZero Tw.O M) (sqProj_comp_sqIncl Tw.O M)).2 φ h1 h2
    choose n hn using fun k => sqKer_surjective (O := Tw.O) (M := M) (m k)
    obtain rfl : m = fun k => sqKer (n k) := funext fun k => (hn k).symm
    refine ⟨n, ⟨fun k => sqKer_injective (O := Tw.O) (M := M) ?_, hm2⟩, fun n' hn' => ?_⟩
    · rw [map_nsmul, map_zero]; exact hm1 k
    · have h := hm3 (fun k => sqKer (n' k))
        ⟨fun k => by rw [← map_nsmul, hn'.1, map_zero], hn'.2⟩
      exact funext fun k => sqKer_injective (O := Tw.O) (M := M) (congrFun h k)
  obtain ⟨φ₀, ⟨h1, h2, h3⟩, -⟩ := H1 _ (lieBasis (Tw.O : Type) p g) fun k => lie_nsmul _
  have key : ∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M]
      (u : LieDualModP p (Tw.O : Type) g →ₗ[(Tw.O : Type)] M),
      B.map ((sqMap u).comp φ₀) (D.fin.y (D.ptIdx 0)) =
        tgPt B Tw.O D.ch.gb fun k => u (lieBasis (Tw.O : Type) p g k) := by
    intro M _ _ u
    rw [B.map_comp, h3]
    exact map_sqMap_tg B _ _ u
  have key2 : ∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (m : Fin g → M)
      (hm : ∀ k, p • m k = 0) (φ : LHom (D.fin.AAx (D.ptIdx 0)) (sqAlg Tw.O M)),
      φ.comp (D.fin.sO (D.ptIdx 0)) = sqIncl Tw.O M → (sqProj Tw.O M).comp φ = D.ptMap 0 →
      B.map φ (D.fin.y (D.ptIdx 0)) = tgPt B Tw.O D.ch.gb m →
      φ = (sqMap (lieLift (Tw.O : Type) m hm)).comp φ₀ := by
    intro M _ _ m hm φ k1 k2 k3
    refine (H1 M m hm).unique ⟨k1, k2, k3⟩
      ⟨sqMap_comp_sO φ₀ h1 _, sqProj_comp_sqMap φ₀ h2 _, ?_⟩
    rw [key]
    simp only [lieLift_basis]
  refine ⟨(SqExt.sndHom (O := (Tw.O : Type)) (M := LieDualModP p (Tw.O : Type) g)).comp
    (φ₀.1.toRingHom.toAddMonoidHom), snd_smul φ₀ h1, snd_leibniz φ₀ h2, ?_, ?_⟩
  · intro M _ _ d d1 d2
    obtain ⟨φ, k1, k2, k3⟩ := exists_lift hε d d1 d2
    obtain ⟨m, ⟨hm1, hm2⟩, hm3⟩ := H2 M φ k1 k2
    refine ⟨lieLift (Tw.O : Type) m hm1, fun f => ?_, fun u hu => lie_ext fun k => ?_⟩
    · rw [← k3, key2 M m hm1 φ k1 k2 hm2]; rfl
    · have hφ : φ = (sqMap u).comp φ₀ := lhom_ext fun f =>
        SqExt.ext (O := (Tw.O : Type)) (M := M)
          (congrArg (fun ψ => ψ.1 f) (k2.trans h2.symm)) ((k3 f).trans (hu f))
      have h := hm3 (fun k => u (lieBasis (Tw.O : Type) p g k))
        ⟨fun k => by rw [← map_nsmul, lie_nsmul, map_zero], by rw [hφ, key]⟩
      rw [lieLift_basis]
      exact congrFun h k
  · intro a α hα1 hα2 f l hl
    have k1 : (φ₀.comp α).comp (D.fin.sO (D.ptIdx 0)) = sqIncl Tw.O _ := by
      rw [← h1]
      exact congrArg φ₀.comp hα1
    have k3 : B.map (φ₀.comp α) (D.fin.y (D.ptIdx 0)) = tgPt B Tw.O D.ch.gb
        fun k => (Submodule.Quotient.mk (D.H.ρL a k) : LieDualModP p (Tw.O : Type) g) := by
      rw [B.map_comp, hα2, D.A.act_nat a _ _ φ₀ h1,
        tg_act D.A a D.ch.gb (lieBasis (Tw.O : Type) p g) (fun k => lie_nsmul _) _ h3]
      simp only [← D.L.ρL_spec, sum_lieBasis]
    have k2 : (sqProj Tw.O _).comp (φ₀.comp α) = D.ptMap 0 := by
      refine huniq' _ ?_ ?_
      · exact (congrArg (sqProj Tw.O _).comp k1).trans (sqProj_comp_sqIncl Tw.O _)
      · rw [B.map_comp, k3]
        exact (B.tg_ker _ _ _).2 ⟨_, rfl⟩
    have h := congrArg (fun ψ => SqExt.snd (O := (Tw.O : Type))
      (M := LieDualModP p (Tw.O : Type) g) (ψ.1 f)) (key2 _ _ (fun k => lie_nsmul _) _ k1 k2 k3)
    refine h.trans ?_
    refine (congrArg (fun x => lieLift (Tw.O : Type)
      (fun k => (Submodule.Quotient.mk (D.H.ρL a k) : LieDualModP p (Tw.O : Type) g))
      (fun k => lie_nsmul _) x) hl).trans ?_
    rw [lieLift_mk]
    have hρ : (D.H.ρL a)ᵀ *ᵥ l = ∑ k, l k • D.H.ρL a k := by
      ext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hρ, ← Submodule.mkQ_apply, map_sum]
    rfl
end GlobalTheory.CotUniv
