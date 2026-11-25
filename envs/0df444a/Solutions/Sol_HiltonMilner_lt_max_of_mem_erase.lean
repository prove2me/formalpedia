-- Prove2me | solution 1 for HiltonMilner.lt_max_of_mem_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:59:12.490917+00:00
-- url     : https://prove2.me/submissions/a19e8057-d5d2-437b-90ad-552bfc67cb42

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {X : Finset ℕ} (hX : X.Nonempty) {y : ℕ} (hy : y ∈ X.erase (X.max' hX)) :
    y < X.max' hX :=
  lt_of_le_of_ne (X.le_max' y (mem_of_mem_erase hy)) (ne_of_mem_erase hy)
end HiltonMilner
