-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:31.493315+00:00
-- url     : https://prove2.me/submissions/08e27526-b947-4476-a7a7-0e8dcdb5c5e3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_pointed
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_transfer
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_exact_of_span
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_finite_chain
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_rho_nat
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_rf_nat
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_loc1
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_loc2
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_uf_bij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {P : Type} [SemilatticeInf P]
variable (s : X ⟶ Sp R) (W : X.affineOpens) (u : P →o X.affineOpens) (hle : ∀ a, (u a).1 ≤ W.1)
include hle
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution [Finite P] (hC : CxSt) (hH : HtpySt) (hinf : ∀ a b, (u (a ⊓ b)).1 = (u a).1 ⊓ (u b).1)
    (hcov : ⨆ a, (u a).1 = W.1) (n : ℕ) (z : Cn (FF s u) (n + 1))
    (hz : dn (FF s u) (n + 1) z = 0) : ∃ y, dn (FF s u) n y = z := by
  have hS : Ideal.span {f : Γ(X, W.1) | ∃ a, X.basicOpen f ≤ (u a).1} = ⊤ := by
    refine (IsAffineOpen.self_le_iSup_basicOpen_iff W.2).1 fun x hx ↦ ?_
    rw [← hcov] at hx
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨f, hf, hxf⟩ := IsAffineOpen.exists_basicOpen_le W.2 (V := (u a).1) ⟨x, ha⟩ (hle a ha)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, a, hf⟩, hxf⟩
  haveI := finite_chain (P := P) (n + 1)
  haveI := finite_chain (P := P) (n + 2)
  refine exact_of_span (FF s u) (fun T ↦ (Sec.res s (hle T.unop)).toRingHom)
    (fun T T' φ b ↦ (Sec.res_res _ _ _ b).symm) _ hS n z ?_
  rintro f ⟨a₀, hf⟩
  exact transfer hC (rho s W u hle f) (rho_nat s W u hle f) (gF s W u hle f)
    (rf_nat s W u hle f) (loc1 s W u hle f) (loc2 s W u hle f) n
    (fun z' hz' ↦ pointed _ a₀ (uf_bij s W u hle hinf f a₀ hf) hH n z' hz') z hz
end GlobalTheory.CompanionTheory.AffAcyc
