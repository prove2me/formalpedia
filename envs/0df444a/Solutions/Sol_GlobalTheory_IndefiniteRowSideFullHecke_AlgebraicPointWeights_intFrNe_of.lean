-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights.intFrNe_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:25.496667+00:00
-- url     : https://prove2.me/submissions/e30c0ec3-a494-4d44-b81c-11556d245c13

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AlgebraicPointWeights
import Theorems.Thm_Formalism_L2_Pj_OverLa_bc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
theorem _root_.solution (h₁ : AlgebraicPointOver Xo c) (h₂ : IntegralFrameAfterExt Xo c) :
    IntFrNe Xo c (fun _ _ y => y.IsAlg) := by
  intro la
  obtain ⟨T, io, e, ho, hT, ⟨y⟩⟩ := h₁ la
  obtain ⟨T', io', φ, r, hr, hv, -, hfin, z, y', t, -, -⟩ := h₂ la T io e ho y
  letI := io.toAlgebra
  letI := io'.toAlgebra
  have hc : (φ : T.Fr →+* T'.Fr).comp io = io' := RingHom.ext fun x => φ.commutes x
  exact ⟨T', io', r * e, hc ▸ ho.bc (φ : T.Fr →+* T'.Fr) hr hv, y', hfin hT⟩
end GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
