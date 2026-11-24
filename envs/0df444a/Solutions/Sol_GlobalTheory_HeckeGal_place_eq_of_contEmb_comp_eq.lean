-- Prove2me | solution 1 for GlobalTheory.HeckeGal.place_eq_of_contEmb_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:21.285256+00:00
-- url     : https://prove2.me/submissions/11fcf1eb-3f5a-4534-a11d-2e94f7bb0ee5

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PlaceEqOfContEmbCompEq
import Theorems.Thm_GlobalTheory_HeckeGal_norm_lt_one_of_contEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory GlobalTheory.HeckeGal
open NumberField IsDedekindDomain
namespace GlobalTheory.HeckeGal
namespace _root_.GlobalTheory.HeckeGal
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (v v' : HeightOneSpectrum (𝓞 E))
      (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (j' : v'.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l),
      Continuous j → Continuous j' →
      j.comp (algebraMap E (v.adicCompletion E)) = j'.comp (algebraMap E (v'.adicCompletion E)) →
      v = v' := by
  intro E _ _ l _ v v' j j' hj hj' hcomp
  by_contra hne
  have hideal : v.asIdeal ≠ v'.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : v.asIdeal ⊔ v'.asIdeal = ⊤ := v.isMaximal.coprime_of_ne v'.isMaximal hideal
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ _)
  have hna := _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb v j hj a ha
  have hnb := _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb v' j' hj' b hb
  have hb' : j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)) =
      j' (algebraMap E (v'.adicCompletion E) (algebraMap (𝓞 E) E b)) :=
    RingHom.congr_fun hcomp _
  rw [← hb'] at hnb
  have hsum : j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a)) +
      j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)) = 1 := by
    rw [← map_add, ← map_add, ← map_add, hab, map_one, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max
    (j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a)))
    (j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)))
  rw [hsum, norm_one] at hle
  exact absurd (hle.trans_lt (max_lt hna hnb)) (lt_irrefl 1)
end _root_.GlobalTheory.HeckeGal
end GlobalTheory.HeckeGal
