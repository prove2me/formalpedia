-- Prove2me | solution 1 for GlobalTheory.DatumCoverAdjoint.datum_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:05.116148+00:00
-- url     : https://prove2.me/submissions/dbe6d48f-711a-4e16-a6ef-ba5b4929e6db

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevelCoverDatumSimilitudeAdjointTransport
import Theorems.Thm_GlobalTheory_DatumCoverAdjoint_span_image_sup_eq_top
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_cHalf_mem
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_cSep_mem
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_dvd_of_modN
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_dvd_right
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_exists_adjoint
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_exists_quot_equiv
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_half_prod
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_levRep_spec
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_mem_of_modN
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_modN_of_dvd
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_root_pow
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_zpow_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DatumCoverAdjoint
open GlobalTheory.DatumInverseCharacter
namespace GlobalTheory.DatumCoverAdjoint
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  intro E _ _ _ H Dw l Xo c n d hM hb ph ψ x₀ hpin g hg
  obtain ⟨-, -, -, -, -, hφ⟩ := hpin
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hb
  have hspan : ∀ (l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H),
      ((l'.M : ℕ) : 𝓞 E) ∈ l'.Mb * l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := fun l' => by
    rw [l'.prod]; exact Ideal.mem_span_singleton_self _
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hbM : d.l₂.Mb ≤ l.Mb := hb ▸ (Ideal.mul_le_inf.trans inf_le_left)
  have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := (Ideal.mul_le_inf.trans inf_le_left) (hspan d.l₂)
  have hmJ : ((d.l₂.M : ℕ) : 𝓞 E) ∈ Mfr l :=
    Ideal.map_mono hbM ((Ideal.mul_le_inf.trans inf_le_right) (hspan d.l₂))
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  set f := g.f d.l₂.M with hf
  obtain ⟨σ, hσ⟩ := exists_quot_equiv Dw hmb f g' hg'
  obtain ⟨fa, hfa⟩ := exists_adjoint Dw f
  obtain ⟨ga, hga⟩ := exists_adjoint Dw g'
  have hsurj : ∀ a, ∃ b, ga b - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    ⟨fa a, mem_of_modN Dw hmJ (modN_of_dvd Dw hM₂ fun v => by
      rw [map_sub, LinearMap.sub_apply, hga, hfa, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).2)⟩
  refine ⟨σ.toEquiv, hσ, fun rk x0 hx => ⟨fun b => ga (x0 b),
    span_image_sup_eq_top (Mfr l) ga hsurj x0 _ hx, fun q => ?_⟩⟩
  have hq : ∀ b, f (levRep (σ.toEquiv.symm (q b))) - levRep (q b) ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro b
    rw [← Submodule.Quotient.eq, ← hσ, levRep_spec, levRep_spec]
    exact σ.apply_symm_apply _
  have hz : zetaM c ^ pairL (l := l) x0 (fun b => levRep (σ.toEquiv.symm (q b))) =
      zetaM c ^ pairL (l := l) (fun b => ga (x0 b)) (fun b => levRep (q b)) := by
    refine zpow_congr hM₁ (root_pow c dvd_rfl) ?_
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [hga, g'.map_smul, ← map_sub, ← smul_sub]
    refine dvd_right Dw l.prod (cSep_mem l) _ ?_
    set a := levRep (σ.toEquiv.symm (q b))
    have h1 : g' (f a - levRep (q b)) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := g') (hq b)
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono hbM le_top this
    have h2 : g' (f a) - a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
      mem_of_modN Dw (hbM hmb) (hg' a).1
    have := sub_mem h1 h2
    convert this using 1
    rw [map_sub]
    abel
  have hroot := root_pow d.c₂ (N := d.pd) (hM ▸ Dvd.intro_left _ rfl)
  have hδ : d.eF (d.φδ (fun b => σ.toEquiv.symm (q b))) = d.eF (d.φδ q) := by
    rw [hφ, hφ]
    refine finsum_congr fun x => ?_
    congr 1
    refine zpow_congr hpd hroot ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [← map_sub, ← smul_sub]
    refine dvd_right Dw hIJ (cHalf_mem d.I) _ ?_
    have := sub_mem (Submodule.smul_mono hbI le_rfl (hq b)) (hg (levRep (σ.toEquiv.symm (q b))))
    convert this using 1
    abel
  unfold DeltaDat.w
  rw [hz, map_mul, map_mul, hδ]
end GlobalTheory.DatumCoverAdjoint
