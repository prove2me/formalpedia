-- Prove2me | solution 1 for HadwigerMader.colorable_two_of_not_isMinor_K3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:07.318185+00:00
-- url     : https://prove2.me/submissions/ed1eca8b-b09b-42f6-9e3b-4517e137d23b

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_HadwigerMader_isMinor_iff_lib
public import Theorems.Thm_CliqueMinors_colorable_two_of_not_isMinor_K3


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}
namespace HadwigerMader
theorem _root_.solution [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) : G.Colorable 2 :=
  CliqueMinors.colorable_two_of_not_isMinor_K3 G (fun h' => h ((isMinor_iff_lib _ G).2 h'))
end HadwigerMader
