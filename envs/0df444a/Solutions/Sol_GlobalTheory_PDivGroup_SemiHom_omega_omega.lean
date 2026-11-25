-- Prove2me | solution 1 for GlobalTheory.PDivGroup.SemiHom.omega_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:33:00.017933+00:00
-- url     : https://prove2.me/submissions/31027249-19bb-42d8-b804-c9fcb5f696f7

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk



set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
open GlobalTheory.PDivGroup.SemiHom
variable {σ : O →+* O'} {τ : O' →+* O''} {G H : PDivGroup p O} {G' H' : PDivGroup p O'}
  {G'' : PDivGroup p O''}
variable (s : SemiHom σ G' G)
variable (t : SemiHom τ G'' G') {ρ : O →+* O''} (u : SemiHom ρ G'' G)
  (h : ∀ n a, u.app n a = t.app n (s.app n a))
include h
namespace GlobalTheory.PDivGroup.SemiHom
theorem _root_.solution (w : G.omega) : t.omega (s.omega w) = u.omega w :=
  Subtype.ext (funext fun n => by
    obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 n)
    simp [← ha, h])
end GlobalTheory.PDivGroup.SemiHom
