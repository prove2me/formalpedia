-- Prove2me | solution 1 for LinearChoresCLS.encoded_basic_price_ratios
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:41:40.320968+00:00
-- url     : https://prove2.me/submissions/de0644a9-ac56-4795-9bb0-8437d1afc4f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch
import Theorems.Thm_CookPvsNP_polyTimeComputable_pairFst
import Theorems.Thm_CookPvsNP_polyTimeComputable_pairSnd
import Theorems.Thm_CookPvsNP_polyTimeComputable_tagged_pair
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp
import Theorems.Thm_LinearChoresCLS_encoded_source_parameters
import Theorems.Thm_LinearChoresCLS_encoded_scaled_price_ratios

open NetworkEquilibriumCLS.LinearNash

theorem solution :
    ∃ g : List (Option (Bool ⊕ Bool)) → List Bool, PolyTime g ∧
      ∀ {n a m : ℕ}, 0 < n → ∀ (P : Quadratic n) (ε : ℚ), 0 < ε →
        ∀ (b : Fin (n+1) → Fin m), (∀ j, (b j).val = j.val) →
        ∀ (p : Fin m → ℚ) (z : Fin a → Fin m → ℚ), 0 < p (b 0) →
        encVector (fun i : Fin n =>
          (1 / ((1/2 : ℚ)^LinearChoresCLS.chainLength P ε)) * (p (b i.succ) / p (b 0) - 1)) =
        g (pairCode (encQuadratic P ++ encRat ε) (LinearChoresCLS.encCE p z)) := by
  obtain ⟨source, hsource_poly, hsource⟩ := LinearChoresCLS.encoded_source_parameters
  obtain ⟨ratios, hratios_poly, hratios⟩ := LinearChoresCLS.encoded_scaled_price_ratios
  obtain ⟨left, hleft_poly, hleft⟩ := CookPvsNP.polyTimeComputable_pairFst Bool Bool
  obtain ⟨right, hright_poly, hright⟩ := CookPvsNP.polyTimeComputable_pairSnd Bool Bool
  let metadata : List (Option (Bool ⊕ Bool)) → List Bool := source ∘ left
  let bundle : List (Option (Bool ⊕ Bool)) → List (Option (Bool ⊕ Bool)) :=
    fun w => pairCode (metadata w) (right w)
  have hmetadata_poly : PolyTime metadata :=
    CookPvsNP.polyTimeComputable_comp left source hleft_poly hsource_poly
  have hbundle_poly : PolyTime bundle := by
    simpa only [bundle, pairCode] using
      CookPvsNP.polyTimeComputable_tagged_pair metadata right hmetadata_poly hright_poly
  refine ⟨ratios ∘ bundle, CookPvsNP.polyTimeComputable_comp bundle ratios hbundle_poly hratios_poly, ?_⟩
  intro n a m hn P ε hε b hb p z hp
  have hleft_pair : left (pairCode (encQuadratic P ++ encRat ε) (LinearChoresCLS.encCE p z)) =
      encQuadratic P ++ encRat ε := by
    simpa only [pairCode] using hleft (encQuadratic P ++ encRat ε) (LinearChoresCLS.encCE p z)
  have hright_pair : right (pairCode (encQuadratic P ++ encRat ε) (LinearChoresCLS.encCE p z)) =
      LinearChoresCLS.encCE p z := by
    simpa only [pairCode] using hright (encQuadratic P ++ encRat ε) (LinearChoresCLS.encCE p z)
  simp only [Function.comp_apply, bundle, metadata, hleft_pair, hright_pair,
    hsource hn P ε hε]
  exact hratios (LinearChoresCLS.chainLength P ε) b hb p z hp
